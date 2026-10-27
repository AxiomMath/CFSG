module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.PSLTwoFstar
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsSevenSevenC
import CFSG.Quasithin.Background.RonanE42Small
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowFstarLift
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HyperplaneOrbit

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

private theorem actOnSub_comp_le {W : Type} [CommGroup W] {A Y : Subgroup (MulAut W)}
    (hAY : A ≤ Y) {I : Subgroup W}
    (hYI : ∀ y ∈ Y, ∀ u ∈ I, y u ∈ I) (hAI : ∀ a ∈ A, ∀ u ∈ I, a u ∈ I) (a : ↥A) :
    actOnSub (W := W) (A := Y) (K := I) hYI ⟨(a : MulAut W), hAY a.2⟩ =
      actOnSub (W := W) (A := A) (K := I) hAI a := by
  rfl

private theorem conj_mem_map_center {G : Type*} [Group G] {L : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (L : Set G)) {c : G}
    (hc : c ∈ (Subgroup.center ↥L).map L.subtype) :
    y * c * y⁻¹ ∈ (Subgroup.center ↥L).map L.subtype := by
  obtain ⟨cL, hcL, rfl⟩ := Subgroup.mem_map.mp hc
  have hconj : y * (cL : G) * y⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hy (cL : G)).mp cL.2
  refine Subgroup.mem_map.mpr ⟨⟨y * (cL : G) * y⁻¹, hconj⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro l
  apply Subtype.ext
  change (l : G) * (y * (cL : G) * y⁻¹) = (y * (cL : G) * y⁻¹) * (l : G)
  have hyl : y⁻¹ * (l : G) * y ∈ L := by
    simpa using (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (L : Set G)).inv_mem hy) (l : G)).mp l.2
  have hcomm : (y⁻¹ * (l : G) * y) * (cL : G) = (cL : G) * (y⁻¹ * (l : G) * y) :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hcL ⟨_, hyl⟩)
  calc (l : G) * (y * (cL : G) * y⁻¹)
      = y * ((y⁻¹ * (l : G) * y) * (cL : G)) * y⁻¹ := by group
    _ = y * ((cL : G) * (y⁻¹ * (l : G) * y)) * y⁻¹ := by rw [hcomm]
    _ = (y * (cL : G) * y⁻¹) * (l : G) := by group

private theorem le_normalizer_map_center {G : Type*} [Group G] {L Y : Subgroup G}
    (hY : Y ≤ Subgroup.normalizer (L : Set G)) {P : Subgroup G}
    (hP : P = (Subgroup.center ↥L).map L.subtype) :
    Y ≤ Subgroup.normalizer (P : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro p
  rw [hP]
  constructor
  · intro hp
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hp
    exact conj_mem_map_center (hY hy) (Subgroup.mem_map.mpr ⟨c, hc, rfl⟩)
  · intro hp
    obtain ⟨c, hc, hcval⟩ := Subgroup.mem_map.mp hp
    have hmem := conj_mem_map_center (L := L) (y := y⁻¹) (Subgroup.inv_mem _ (hY hy))
      (Subgroup.mem_map.mpr ⟨c, hc, rfl⟩)
    rw [hcval] at hmem
    rwa [show y⁻¹ * (y * p * y⁻¹) * (y⁻¹)⁻¹ = p by group] at hmem

theorem aParam_le_of_fstar_sl2
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} {F : Type} [Field F] [Finite F] (hF2 : (2 : F) ≠ 0)
    (h3 : 3 < Nat.card F) (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal) (hFs : Fstar Y = L)
    (e : ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    (9 < Nat.card F → E3.aParam Y ≤ 1) ∧ E3.aParam Y ≤ 2 := by
  classical
  have h4 : 4 ≤ Nat.card F := by omega
  have hLq : CFSG.IsQuasisimple ↥L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      (CFSG.Quasithin.C126.Nat.isQuasisimple_sl2 h4)
  let zL : ↥L := e.symm (-1)
  let z : MulAut W := zL
  have hcenterL : Subgroup.center ↥L = Subgroup.zpowers zL :=
    CFSG.Monster.Spin.center_eq_zpowers_of_mulEquiv e.symm
      (CFSG.ClassicalInvolution.QuaternionStructure.center_specialLinearGroup_two_eq_zpowers hF2)
  have hzLc : zL ∈ Subgroup.center ↥L := by
    rw [hcenterL]
    exact Subgroup.mem_zpowers zL
  have hzLorder : orderOf zL = 2 :=
    (MulEquiv.orderOf_eq e.symm (-1)).trans
      (CFSG.ClassicalInvolution.QuaternionStructure.orderOf_neg_one_specialLinearGroup_two hF2)
  have hzorder : orderOf z = 2 := by
    rw [show z = (zL : MulAut W) from rfl, Subgroup.orderOf_coe]
    exact hzLorder
  have hzY : z ∈ Y := hLY zL.2
  let zY : ↥Y := ⟨z, hzY⟩
  have hzYorder : orderOf zY = 2 := by
    rw [← Subgroup.orderOf_coe zY]
    exact hzorder
  have hzYcard : Nat.card (Subgroup.zpowers zY) = 2 := by
    rw [Nat.card_zpowers, hzYorder]
  set P : Subgroup (MulAut W) := Subgroup.zpowers z
  have hP2 : IsPGroup 2 ↥P :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzorder]; norm_num)
  have hzcent : z ∈ Subgroup.centralizer (L : Set (MulAut W)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp hzLc ⟨l, hl⟩)
  have hPL : P ≤ Subgroup.centralizer (L : Set (MulAut W)) := Subgroup.zpowers_le.mpr hzcent
  have hPn : L ≤ Subgroup.normalizer (P : Set (MulAut W)) :=
    ((Subgroup.le_centralizer_iff).mp hPL).trans (Subgroup.centralizer_le_normalizer _)
  have hYnormL : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp hLn
  have hzP : z ∈ P := Subgroup.mem_zpowers z
  have hmap_center : (Subgroup.center ↥L).map L.subtype = P := by
    rw [hcenterL, MonoidHom.map_zpowers]
    rfl
  have hYnP : Y ≤ Subgroup.normalizer (P : Set (MulAut W)) :=
    le_normalizer_map_center hYnormL hmap_center.symm
  set U : Subgroup W := fixV P with hU
  have hYI : ∀ y ∈ Y, ∀ u ∈ U, y u ∈ U := SevenSevenC.stableUnder_fixV_of_le_normalizer hYnP
  have hUW : ∀ u : ↥U, u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hW (u : W))
  let ρ : ↥Y →* MulAut ↥U := actOnSub hYI
  let Ystar : Subgroup (MulAut ↥U) := ρ.range
  let Lstar : Subgroup (MulAut ↥U) := (L.subgroupOf Y).map ρ
  have hLstar_le : Lstar ≤ Ystar := Subgroup.map_le_range ρ _
  have hρz : ρ zY = 1 := by
    ext u
    rw [show ((ρ zY) u : W) = ((zY : ↥Y) : MulAut W) (u : W) from actOnSub_apply hYI zY u]
    exact mem_fixV.mp u.2 z hzP
  have hzYker : zY ∈ ρ.ker := MonoidHom.mem_ker.mpr hρz
  have hzpow_iff : ∀ l : ↥L,
      (⟨(l : MulAut W), hLY l.2⟩ : ↥Y) ∈ Subgroup.zpowers zY ↔
        l ∈ Subgroup.zpowers zL := by
    intro l
    rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, Subtype.ext ?_⟩
      have := congrArg Subtype.val hk
      simpa [zY, z] using this
    · rintro ⟨k, hk⟩
      refine ⟨k, Subtype.ext ?_⟩
      have := congrArg Subtype.val hk
      simpa [zY, z] using this
  have hker_le : ρ.ker ≤ Subgroup.zpowers zY := by
    intro y hy
    have hρy : ρ y = 1 := MonoidHom.mem_ker.mp hy
    have hcomm : ∀ (l : MulAut W) (hl : l ∈ L),
        actOnSub (SevenSevenC.stableUnder_fixV_of_le_normalizer hYnP) ⟨(y : MulAut W), y.2⟩ *
          actOnSub (SevenSevenC.stableUnder_fixV_of_le_normalizer hPn) ⟨l, hl⟩ =
        actOnSub (SevenSevenC.stableUnder_fixV_of_le_normalizer hPn) ⟨l, hl⟩ *
          actOnSub (SevenSevenC.stableUnder_fixV_of_le_normalizer hYnP) ⟨(y : MulAut W), y.2⟩ := by
      intro l hl
      have h1 : actOnSub (SevenSevenC.stableUnder_fixV_of_le_normalizer hYnP)
          ⟨(y : MulAut W), y.2⟩ = 1 := hρy
      rw [h1, one_mul, mul_one]
    have hycent : ((y : ↥Y) : MulAut W) ∈ Subgroup.centralizer (L : Set (MulAut W)) :=
      SevenSevenC.centralizes_of_commutes_on_fixV hW hLq hP2 hPL hPn hLY hYnP y.2
        (hYnormL y.2) hcomm
    have hyL : ((y : ↥Y) : MulAut W) ∈ L :=
      W4Row.mem_of_mem_centralizer_of_fstar_eq hLY hFs y.2 hycent
    have hyc : (⟨((y : ↥Y) : MulAut W), hyL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hycent (l : MulAut W) l.2
    have hz : (⟨((y : ↥Y) : MulAut W), hyL⟩ : ↥L) ∈ Subgroup.zpowers zL := by
      rw [← hcenterL]
      exact hyc
    rw [Subgroup.mem_zpowers_iff] at hz ⊢
    obtain ⟨k, hk⟩ := hz
    exact ⟨k, Subtype.ext (by simpa [zY, z] using congrArg Subtype.val hk)⟩
  have hker : ρ.ker = Subgroup.zpowers zY :=
    le_antisymm hker_le (Subgroup.zpowers_le.mpr hzYker)
  let ψ : ↥L →* ↥Lstar :=
    { toFun := fun l => ⟨ρ ⟨(l : MulAut W), hLY l.2⟩,
        Subgroup.mem_map.mpr ⟨⟨(l : MulAut W), hLY l.2⟩,
          Subgroup.mem_subgroupOf.mpr l.2, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        change ρ (⟨((1 : ↥L) : MulAut W), hLY (1 : ↥L).2⟩ : ↥Y) = 1
        rw [show (⟨((1 : ↥L) : MulAut W), hLY (1 : ↥L).2⟩ : ↥Y) = 1 from Subtype.ext rfl,
          map_one]
      map_mul' := by
        intro a b
        apply Subtype.ext
        change ρ (⟨((a * b : ↥L) : MulAut W), hLY (a * b).2⟩ : ↥Y) =
          ρ (⟨(a : MulAut W), hLY a.2⟩ : ↥Y) * ρ (⟨(b : MulAut W), hLY b.2⟩ : ↥Y)
        rw [show (⟨((a * b : ↥L) : MulAut W), hLY (a * b).2⟩ : ↥Y) =
            (⟨(a : MulAut W), hLY a.2⟩ : ↥Y) * ⟨(b : MulAut W), hLY b.2⟩ from
          Subtype.ext rfl, map_mul] }
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
    refine ⟨⟨(y : MulAut W), Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
    apply Subtype.ext
    change ρ (⟨(y : MulAut W), hLY (Subgroup.mem_subgroupOf.mp hy)⟩ : ↥Y) = x
    rw [show (⟨(y : MulAut W), hLY (Subgroup.mem_subgroupOf.mp hy)⟩ : ↥Y) = y from
      Subtype.ext rfl, hxy]
  have hψker : ψ.ker = Subgroup.center ↥L := by
    ext l
    rw [MonoidHom.mem_ker, hcenterL]
    constructor
    · intro hl
      have h1 : ρ (⟨(l : MulAut W), hLY l.2⟩ : ↥Y) = 1 := by
        have := congrArg Subtype.val hl
        simpa [ψ] using this
      have hmem : (⟨(l : MulAut W), hLY l.2⟩ : ↥Y) ∈ ρ.ker := MonoidHom.mem_ker.mpr h1
      rw [hker] at hmem
      exact (hzpow_iff l).mp hmem
    · intro hl
      have hmem : (⟨(l : MulAut W), hLY l.2⟩ : ↥Y) ∈ Subgroup.zpowers zY :=
        (hzpow_iff l).mpr hl
      rw [← hker] at hmem
      have h1 : ρ (⟨(l : MulAut W), hLY l.2⟩ : ↥Y) = 1 := MonoidHom.mem_ker.mp hmem
      apply Subtype.ext
      change ρ (⟨(l : MulAut W), hLY l.2⟩ : ↥Y) = 1
      exact h1
  let e₁ : ↥Lstar ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hψker).trans
        (QuotientGroup.congr (Subgroup.center ↥L)
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) e (Subgroup.map_center_eq e)))
  have hqLstar : CFSG.IsQuasisimple ↥Lstar :=
    CFSG.LocalCores.isQuasisimple_of_surjective hLq ψ hψsurj (by rw [hψker])
  have hconjStar : ∀ x ∈ Ystar, ∀ l ∈ Lstar, x * l * x⁻¹ ∈ Lstar := by
    intro x hx l hl
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
    obtain ⟨l', hl', rfl⟩ := Subgroup.mem_map.mp hl
    have hyl : ((y : ↥Y) * l' * (y : ↥Y)⁻¹) ∈ L.subgroupOf Y := by
      rw [Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_normalizer_iff.mp (hYnormL y.2) (l' : MulAut W)).mp
        (Subgroup.mem_subgroupOf.mp hl')
    rw [← map_mul, ← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem ρ hyl
  have hYstar_norm : Ystar ≤ Subgroup.normalizer (Lstar : Set (MulAut ↥U)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro l
    constructor
    · exact hconjStar x hx l
    · intro hl
      have h := hconjStar x⁻¹ (Ystar.inv_mem hx) (x * l * x⁻¹) hl
      rwa [show x⁻¹ * (x * l * x⁻¹) * (x⁻¹)⁻¹ = l by group] at h
  have hNstar : (Lstar.subgroupOf Ystar).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hYstar_norm
  have hcentStar : Subgroup.centralizer ((Lstar.subgroupOf Ystar : Subgroup ↥Ystar) :
      Set ↥Ystar) ≤ Lstar.subgroupOf Ystar := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨y, hyx⟩ := MonoidHom.mem_range.mp x.2
    have hxeq : x = ⟨ρ y, MonoidHom.mem_range.mpr ⟨y, rfl⟩⟩ := Subtype.ext hyx.symm
    rw [hxeq] at hx ⊢
    have hcomm : ∀ (l : MulAut W) (hl : l ∈ L),
        actOnSub (SevenSevenC.stableUnder_fixV_of_le_normalizer hYnP)
            ⟨(y : MulAut W), y.2⟩ *
          actOnSub (SevenSevenC.stableUnder_fixV_of_le_normalizer hPn) ⟨l, hl⟩ =
        actOnSub (SevenSevenC.stableUnder_fixV_of_le_normalizer hPn) ⟨l, hl⟩ *
          actOnSub (SevenSevenC.stableUnder_fixV_of_le_normalizer hYnP)
            ⟨(y : MulAut W), y.2⟩ := by
      intro l hl
      have hmemL : ρ (⟨(l : MulAut W), hLY hl⟩ : ↥Y) ∈ Lstar :=
        Subgroup.mem_map.mpr ⟨⟨(l : MulAut W), hLY hl⟩,
          Subgroup.mem_subgroupOf.mpr hl, rfl⟩
      have hxl : (⟨ρ (⟨(l : MulAut W), hLY hl⟩ : ↥Y), hLstar_le hmemL⟩ : ↥Ystar) ∈
          Lstar.subgroupOf Ystar := Subgroup.mem_subgroupOf.mpr hmemL
      have hval : ρ (⟨(l : MulAut W), hLY hl⟩ : ↥Y) *
          ρ (⟨(y : MulAut W), y.2⟩ : ↥Y) =
          ρ (⟨(y : MulAut W), y.2⟩ : ↥Y) *
            ρ (⟨(l : MulAut W), hLY hl⟩ : ↥Y) :=
        congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx
          ⟨ρ (⟨(l : MulAut W), hLY hl⟩ : ↥Y), hLstar_le hmemL⟩ hxl)
      change ρ (⟨(y : MulAut W), y.2⟩ : ↥Y) *
          actOnSub (SevenSevenC.stableUnder_fixV_of_le_normalizer hPn) ⟨l, hl⟩ =
        actOnSub (SevenSevenC.stableUnder_fixV_of_le_normalizer hPn) ⟨l, hl⟩ *
          ρ (⟨(y : MulAut W), y.2⟩ : ↥Y)
      rw [show actOnSub (SevenSevenC.stableUnder_fixV_of_le_normalizer hPn) ⟨l, hl⟩ =
          ρ (⟨(l : MulAut W), hLY hl⟩ : ↥Y) from
        (actOnSub_comp_le hLY hYI
          (SevenSevenC.stableUnder_fixV_of_le_normalizer hPn) ⟨l, hl⟩).symm]
      exact hval.symm
    have hycent : ((y : ↥Y) : MulAut W) ∈ Subgroup.centralizer (L : Set (MulAut W)) :=
      SevenSevenC.centralizes_of_commutes_on_fixV hW hLq hP2 hPL hPn hLY hYnP y.2
        (hYnormL y.2) hcomm
    have hyL : ((y : ↥Y) : MulAut W) ∈ L :=
      W4Row.mem_of_mem_centralizer_of_fstar_eq hLY hFs y.2 hycent
    exact Subgroup.mem_map.mpr ⟨y, Subgroup.mem_subgroupOf.mpr hyL, rfl⟩
  have hFstar : Fstar Ystar = Lstar := by
    have h := SevenSevenC.fstarSubOf_eq_of_centralizer_le hLstar_le hqLstar hNstar hcentStar
    rw [fstarSubOf] at h
    have h' := congrArg (Subgroup.map (Subgroup.subtype Ystar)) h
    have hle : Fstar Ystar ≤ Ystar :=
      Subgroup.map_subtype_le (CFSG.Open.genFittingFStar ↥Ystar)
    rw [Subgroup.map_subgroupOf_eq_of_le hle,
      Subgroup.map_subgroupOf_eq_of_le hLstar_le] at h'
    exact h'
  have hmain : (9 < Nat.card F → E3.aParam Ystar ≤ 1) ∧ E3.aParam Ystar ≤ 2 :=
    aParam_le_of_fstar_psl2 (W := ↥U) hUW hF2 h3 hLstar_le hNstar hFstar e₁
  have hNoMem : ∀ {k : ℕ}, 2 ≤ k → (∀ B : Subgroup (MulAut ↥U), B ∉ E3.aSet k Ystar) →
      ∀ A : Subgroup (MulAut W), A ∉ E3.aSet k Y := by
    intro k hk hEmpty A hA
    have hAI : ∀ a ∈ A, ∀ u ∈ U, a u ∈ U := fun a ha => hYI a (hA.1 ha)
    have hle : (actOnSub (W := W) (A := A) (K := U) hAI).range ≤ Ystar := by
      rintro _ ⟨a, rfl⟩
      exact MonoidHom.mem_range.mpr ⟨⟨(a : MulAut W), hA.1 a.2⟩,
        (actOnSub_comp_le hA.1 hYI hAI a).symm⟩
    have hne : (actOnSub (W := W) (A := A) (K := U) hAI).range ≠ ⊥ := by
      intro hbot
      have hAle : A.subgroupOf Y ≤ ρ.ker := by
        intro y hy
        rw [Subgroup.mem_subgroupOf] at hy
        rw [MonoidHom.mem_ker]
        have h2 : actOnSub (W := W) (A := A) (K := U) hAI ⟨(y : MulAut W), hy⟩ = 1 := by
          have hmem : actOnSub (W := W) (A := A) (K := U) hAI ⟨(y : MulAut W), hy⟩ ∈
              (actOnSub (W := W) (A := A) (K := U) hAI).range :=
            MonoidHom.mem_range.mpr ⟨_, rfl⟩
          rw [hbot] at hmem
          simpa using Subgroup.mem_bot.mp hmem
        have h3 := actOnSub_comp_le hA.1 hYI hAI ⟨(y : MulAut W), hy⟩
        rw [show (⟨(y : MulAut W), hA.1 hy⟩ : ↥Y) = y from Subtype.ext rfl] at h3
        exact h3.trans h2
      have hcard_le : Nat.card (A.subgroupOf Y) ≤ 2 := by
        have h := Subgroup.card_dvd_of_le hAle
        rw [hker, hzYcard] at h
        exact Nat.le_of_dvd (by norm_num) h
      have hcard_eq : Nat.card (A.subgroupOf Y) = Nat.card A :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA.1).toEquiv
      have hA2 : IsPGroup 2 A := E3.isPGroup_of_isElemAbelian2 hA.2.2.1
      have hcardA : Nat.card A = 2 ^ E3.mQuot A ⊥ := by
        rw [← Subgroup.relIndex_bot_left (H := A), E3.relIndex_eq_two_pow hA2 ⊥]
      have hm : 2 ≤ E3.mQuot A ⊥ := hk.trans (E3.le_mQuot_bot_of_mem_aSet hA)
      have h4le : 4 ≤ Nat.card A := by
        rw [hcardA]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ E3.mQuot A ⊥ := Nat.pow_le_pow_right (by norm_num) hm
      omega
    exact hEmpty _ (E3.mem_aSet_actOnSub hA hAI hle hne)
  have hNoStar3 : ∀ B : Subgroup (MulAut ↥U), B ∉ E3.aSet 3 Ystar := by
    intro B hB
    have hle := E3.le_aParam_of_mem_aSet (by norm_num : 0 < 3) hB
    omega
  have hno3 : ∀ A : Subgroup (MulAut W), A ∉ E3.aSet 3 Y :=
    hNoMem (by norm_num) hNoStar3
  have htwo : E3.aParam Y ≤ 2 :=
    CFSG.Quasithin.RonanE42.aParam_le_of_aSet_empty Y 2 hno3
  refine ⟨fun h9 => ?_, htwo⟩
  have hNoStar2 : ∀ B : Subgroup (MulAut ↥U), B ∉ E3.aSet 2 Ystar := by
    intro B hB
    have hle := E3.le_aParam_of_mem_aSet (by norm_num : 0 < 2) hB
    have hle1 := hmain.1 h9
    omega
  exact CFSG.Quasithin.RonanE42.aParam_le_of_aSet_empty Y 1 (hNoMem le_rfl hNoStar2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

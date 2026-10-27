module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Kernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Std
public import CFSG.LocalAnalysis.StronglyEmbedded.PSubgroups

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_card_of_natOmegaMinus {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} (h : NatOmegaMinus H (⊤ : Subgroup W) ⊥ 6 1) :
    Nat.card W = 64 := by
  obtain ⟨K, hK, hKf, b, c, hK2, hpoly, β, hβ⟩ := natOmegaMinus_exists_eichler h
  rw [Nat.card_congr β.toEquiv,
    Nat.card_congr (Multiplicative.toAdd :
      Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) ≃
        (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K)),
    Nat.card_fun, hK2]
  simp only [Nat.card_sum, Nat.card_fin]
  norm_num

theorem s16c1_card_V_of_case (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Case167_1 D ⊥ V hV L) : Nat.card ↥V = 64 := by
  have h := s16c1_card_of_natOmegaMinus (W := Vtil ⊥ V hV) (H := lBar ⊥ V hV L) hc.2.1
  rw [← h]
  exact Nat.card_congr (TwelveShort.mkTilEquiv V hV).toEquiv

theorem s16c1_cent_le_M {M V : Subgroup G} (hV : IsElemAbelian 2 V) (hV64 : Nat.card ↥V = 64)
    (hr : (4 : ℕ∞) < rMV M V) {A : Subgroup G} (hAV : A ≤ V) (hA : 4 ≤ Nat.card ↥A) :
    centralizer (A : Set G) ≤ M := by
  by_contra hAM
  have hmem : A ∈ {U : Subgroup G | U ≤ V ∧ ¬ centralizer (U : Set G) ≤ M} := ⟨hAV, hAM⟩
  have hle : rMV M V ≤ (E3.mQuot V A : ℕ∞) := by
    rw [rMV]
    exact iInf₂_le A hmem
  have hcard := E3.card_eq_two_pow_mul (V := V) (U := A) hV.isPGroup hAV
  have h64 : 2 ^ E3.mQuot V A * Nat.card ↥A = 64 := by
    rw [← hcard]
    exact hV64
  have hq4 : E3.mQuot V A ≤ 4 := by
    by_contra h
    have h5 : 5 ≤ E3.mQuot V A := by omega
    have hpow : 2 ^ 5 ≤ 2 ^ E3.mQuot V A := Nat.pow_le_pow_right (by norm_num) h5
    nlinarith [hpow, h64, hA]
  have h4 : rMV M V ≤ (4 : ℕ∞) := hle.trans (ENat.natCast_le_natCast.mpr hq4)
  exact absurd h4 (not_le_of_gt hr)

theorem s16c1_cent_conj_le {M V : Subgroup G} (hV : IsElemAbelian 2 V) (hV64 : Nat.card ↥V = 64)
    (hr : (4 : ℕ∞) < rMV M V) {h : G} {A : Subgroup G} (hAV : A ≤ conjSubgroup V h)
    (hA : 4 ≤ Nat.card ↥A) : centralizer (A : Set G) ≤ conjSubgroup M h := by
  set A' : Subgroup G := conjSubgroup A h⁻¹ with hA'def
  have hA'V : A' ≤ V := by
    have h1 : A' ≤ conjSubgroup (conjSubgroup V h) h⁻¹ := by
      rw [hA'def]
      exact E3.conjSubgroup_mono_left h⁻¹ hAV
    rwa [E3.conjSubgroup_conj_inv] at h1
  have hcard : Nat.card ↥A' = Nat.card ↥A := E3.card_conjSubgroup A h⁻¹
  have hA' : 4 ≤ Nat.card ↥A' := by rw [hcard]; exact hA
  have hle : centralizer (A' : Set G) ≤ M := s16c1_cent_le_M hV hV64 hr hA'V hA'
  calc centralizer (A : Set G)
      = centralizer (conjSubgroup A' h : Set G) := by
        congr 1
        rw [hA'def, E3.conjSubgroup_inv_conj]
    _ = conjSubgroup (centralizer (A' : Set G)) h := (E3.conjSubgroup_centralizer A' h).symm
    _ ≤ conjSubgroup M h := E3.conjSubgroup_mono_left h hle

theorem s16c1_exists_three_cent_plane (D : Data G) (hkit : OmegaKit) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D ⊥ V L hV) (hc : Case167_1 D ⊥ V hV L)
    {P : Subgroup G} (hPV : P ≤ V) (hP : Nat.card ↥P = 4) :
    ∃ R : Subgroup G, R ≤ L ∧ IsPGroup 3 R ∧ R ≠ ⊥ ∧ R ≤ centralizer (P : Set G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P' : Subgroup (IntMod V hV) := P.subgroupOf V
  let Ptil : Subgroup (Vtil ⊥ V hV) := P'.map (mkTil ⊥ V hV)
  have hmkTil_inj : Function.Injective (mkTil ⊥ V hV) := by
    intro x y hxy
    exact (TwelveShort.mkTilEquiv V hV).injective (by
      rw [TwelveShort.mkTilEquiv_apply, TwelveShort.mkTilEquiv_apply]
      exact hxy)
  have hP'card : Nat.card ↥P' = 4 := by
    change Nat.card ↥(P.subgroupOf V) = 4
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPV).toEquiv]
    exact hP
  have hPtilcard : Nat.card ↥Ptil = 4 := by
    change Nat.card ↥(P'.map (mkTil ⊥ V hV)) = 4
    rw [Subgroup.card_map_of_injective hmkTil_inj, hP'card]
  obtain ⟨φ, hφmem, hφord, hφfix⟩ :=
    (hkit (Vtil ⊥ V hV) (lBar ⊥ V hV L) hc.2.1).1 Ptil hPtilcard
  let f : ↥L →* MulAut (Vtil ⊥ V hV) :=
    (actTil ⊥ V hV).comp (Subgroup.inclusion (s16c1_le_stabTil D hS))
  have hfrange : f.range = lBar ⊥ V hV L := by
    show ((actTil ⊥ V hV).comp (Subgroup.inclusion (s16c1_le_stabTil D hS))).range =
      lBar ⊥ V hV L
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hE3 : IsPGroup 3 (Subgroup.zpowers φ) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hφord]; norm_num)
  have hEf : Subgroup.zpowers φ ≤ f.range := by
    rw [hfrange]
    exact Subgroup.zpowers_le.mpr hφmem
  obtain ⟨R₀, hR₀pg, hR₀map⟩ :=
    exists_pGroup_map_eq (p := 3) f (Subgroup.zpowers φ) hE3 hEf
  refine ⟨R₀.map L.subtype, ?_, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hr
    exact x.2
  · exact hR₀pg.map L.subtype
  · intro hbot
    have hR₀bot : R₀ = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective R₀ (f := L.subtype)
        L.subtype_injective).mp hbot
    have hzbot : Subgroup.zpowers φ = ⊥ := by
      rw [← hR₀map, hR₀bot, Subgroup.map_bot]
    have hφ1 : φ = 1 := Subgroup.mem_bot.mp (hzbot ▸ Subgroup.mem_zpowers φ)
    rw [hφ1, orderOf_one] at hφord
    omega
  · intro r hr
    obtain ⟨x, hxR₀, rfl⟩ := Subgroup.mem_map.mp hr
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hpV : p ∈ V := hPV hp
    let q : Vtil ⊥ V hV := mkTil ⊥ V hV (IntMod.mk hV ⟨p, hpV⟩)
    have hqP : q ∈ Ptil := by
      change q ∈ P'.map (mkTil ⊥ V hV)
      refine Subgroup.mem_map.mpr ⟨IntMod.mk hV ⟨p, hpV⟩, ?_, rfl⟩
      show p ∈ P
      exact hp
    have hφq : φ q = q := hφfix q hqP
    have hstab : Subgroup.zpowers φ ≤
        MulAction.stabilizer (MulAut (Vtil ⊥ V hV)) q :=
      Subgroup.zpowers_le.mpr (by
        rw [MulAction.mem_stabilizer_iff]
        simpa using hφq)
    have hfx : f x ∈ Subgroup.zpowers φ := by
      rw [← hR₀map]
      exact Subgroup.mem_map.mpr ⟨x, hxR₀, rfl⟩
    have hfxq : f x q = q := by
      have := MulAction.mem_stabilizer_iff.mp (hstab hfx)
      simpa using this
    let g : ↥(stabTil ⊥ V) := ⟨(x : G), s16c1_le_stabTil D hS x.2⟩
    have hfg : f x = actTil ⊥ V hV g := rfl
    have haq : actTil ⊥ V hV g q = q := by rwa [← hfg]
    have hqeq : mkTil ⊥ V hV (actStab ⊥ V hV g (IntMod.mk hV ⟨p, hpV⟩)) =
        mkTil ⊥ V hV (IntMod.mk hV ⟨p, hpV⟩) := by
      rw [← actTil_mk]
      exact haq
    have hmem := (mkTil_eq_iff ⊥ V hV _ _).mp hqeq
    have hone : (actStab ⊥ V hV g (IntMod.mk hV ⟨p, hpV⟩)).val *
        (IntMod.mk hV ⟨p, hpV⟩).val⁻¹ = 1 := Subgroup.mem_bot.mp hmem
    have hval : (actStab ⊥ V hV g (IntMod.mk hV ⟨p, hpV⟩)).val =
        (IntMod.mk hV ⟨p, hpV⟩).val := mul_inv_eq_one.mp hone
    rw [actStab_apply_val] at hval
    have hconj : (x : G) * p * (x : G)⁻¹ = p := by
      have h2 : (g : G) = (x : G) := rfl
      rw [h2] at hval
      simpa only [IntMod.mk, IntMod.val] using hval
    calc p * (x : G) = ((x : G) * p * (x : G)⁻¹) * (x : G) := by rw [hconj]
      _ = (x : G) * p := by group

theorem s16c1_plane_mem_M (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (hkit : OmegaKit) {V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D ⊥ V L hV)
    (hc : Case167_1 D ⊥ V hV L) (hr : (4 : ℕ∞) < rMV D.M V) {h : G} {P : Subgroup G}
    (hPV : P ≤ V) (hP : Nat.card ↥P = 4) (hPh : P ≤ conjSubgroup V h) : h ∈ D.M := by
  by_contra hnot
  have hV64 : Nat.card ↥V = 64 := s16c1_card_V_of_case D hc
  obtain ⟨R, hRL, hRpg, hRne, hRcent⟩ :=
    s16c1_exists_three_cent_plane D hkit hS hc hPV hP
  have hRM : R ≤ D.M := hRL.trans hS.setting.hyp151.le
  have hPcent : centralizer (P : Set G) ≤ conjSubgroup D.M h :=
    s16c1_cent_conj_le hV hV64 hr hPh (by rw [hP])
  have hRconj : R ≤ conjSubgroup D.M h := hRcent.trans hPcent
  have hRconj' : R ≤ D.M.map (MulAut.conj h⁻¹).toMonoidHom := by
    simpa only [conjSubgroup] using hRconj
  have hsp : IsStronglyPEmbedded 3 D.M :=
    isStronglyPEmbedded_three D hSg h1219 hc.2.2.1
  have hdisj := hsp.inf_map_conj_eq_bot Nat.prime_three hRM hRpg h⁻¹
    (fun hh => hnot (by simpa using D.M.inv_mem hh))
  have hle : R ≤ R ⊓ D.M.map (MulAut.conj h⁻¹).toMonoidHom := le_inf le_rfl hRconj'
  rw [hdisj] at hle
  exact hRne (le_bot_iff.mp hle)

private theorem s16c1_eq_one_or_eq_of_mem_zpowers {a b : G} (ha : a ^ 2 = 1)
    (hb : b ∈ Subgroup.zpowers a) : b = 1 ∨ b = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have h2 : a ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact ha
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]

theorem s16c1_card_sup_zpowers {z w : G} (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) (hw2 : w ^ 2 = 1)
    (hzw : z * w = w * z) (hw : w ∉ Subgroup.zpowers z) :
    Nat.card ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers w) = 4 := by
  have hw1 : w ≠ 1 := fun h => hw (by rw [h]; exact Subgroup.one_mem _)
  have hwz : w ≠ z := fun h => hw (by rw [h]; exact Subgroup.mem_zpowers z)
  have hcomm : ∀ a ∈ Subgroup.zpowers z, ∀ b ∈ Subgroup.zpowers w, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow hzw m n).eq
  have hprod := CFSG.Quasithin.B2F.card_sup_mul_card_inf_of_commute
    (A := Subgroup.zpowers z) (B := Subgroup.zpowers w) hcomm
  have hcz : Nat.card ↥(Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1]
  have hcw : Nat.card ↥(Subgroup.zpowers w) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hw2 hw1]
  have hinf : Subgroup.zpowers z ⊓ Subgroup.zpowers w = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    rcases s16c1_eq_one_or_eq_of_mem_zpowers hz2 hy.1 with h1 | h1
    · exact h1
    · exfalso
      have hzW : z ∈ Subgroup.zpowers w := h1 ▸ hy.2
      have hle : Subgroup.zpowers z ≤ Subgroup.zpowers w := Subgroup.zpowers_le.mpr hzW
      have heq : Subgroup.zpowers z = Subgroup.zpowers w :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hcz, hcw])
      exact hw (by rw [heq]; exact Subgroup.mem_zpowers w)
  rw [hinf, Subgroup.card_bot, hcz, hcw] at hprod
  omega

theorem s16c1_core_bot (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (hkit : OmegaKit) {V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D ⊥ V L hV)
    (hc : Case167_1 D ⊥ V hV L) (hr : (4 : ℕ∞) < rMV D.M V) {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) :
    ∀ h ∈ centralizer ({z} : Set G),
      ¬ uOne V z ⊓ conjSubgroup (uOne V z) h ≤ Subgroup.zpowers z → h ∈ D.M := by
  intro h hh hnot
  rw [SetLike.not_le_iff_exists] at hnot
  obtain ⟨w, hw, hwz⟩ := hnot
  have hwV : w ∈ V := (show uOne V z ≤ V from inf_le_left) hw.1
  have hz2 : z ^ 2 = 1 := hV.2 z hz
  have hw2 : w ^ 2 = 1 := hV.2 w hwV
  have hzw : z * w = w * z := by
    have h := IntMod.val_comm (hV := hV) (IntMod.mk hV ⟨z, hz⟩) (IntMod.mk hV ⟨w, hwV⟩)
    simpa only [IntMod.mk, IntMod.val] using h
  have hwconj : w ∈ conjSubgroup V h :=
    (E3.conjSubgroup_mono_left h (show uOne V z ≤ V from inf_le_left)) hw.2
  have hhz : h * z * h⁻¹ = z := by
    have hc : z * h = h * z := (Subgroup.mem_centralizer_iff.mp hh) z (by simp)
    rw [← hc]
    group
  have hzconj : z ∈ conjSubgroup V h := by
    rw [mem_conjSubgroup_iff]
    rwa [hhz]
  have hPV : Subgroup.zpowers z ⊔ Subgroup.zpowers w ≤ V :=
    sup_le (Subgroup.zpowers_le.mpr hz) (Subgroup.zpowers_le.mpr hwV)
  have hPh : Subgroup.zpowers z ⊔ Subgroup.zpowers w ≤ conjSubgroup V h :=
    sup_le (Subgroup.zpowers_le.mpr hzconj) (Subgroup.zpowers_le.mpr hwconj)
  exact s16c1_plane_mem_M D hSg h1219 hkit hS hc hr hPV
    (s16c1_card_sup_zpowers hz1 hz2 hw2 hzw hwz) hPh

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

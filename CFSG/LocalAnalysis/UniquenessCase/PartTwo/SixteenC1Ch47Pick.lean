module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Ch47Conj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Ch47Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Ne47A
public import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBYNonfusedCoreInvolution

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_ne_V_of_sect16 {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) : V₀ ≠ V := by
  intro h
  by_cases hne : V₀ = ⊥
  · exact hS.setting.hyp151.hyp125.pairFacts.ne_bot (h ▸ hne)
  · have h0 := s16c1_inCalV0_of_sect16 hS hne
    exact h0.2.2.2.2.1 (h ▸ h0.2.2.2.1)

theorem s16c1_inter_ne_bot (D : Data G) {V₀ V : Subgroup G} (hV : InCalV D.M V) (hle : V₀ ≤ V)
    (hne : V₀ ≠ V) {g : G} (hO : InCalOStar 1 D.M V₀ V g) : V ⊓ conjSubgroup V g ≠ ⊥ := by
  intro hbot
  obtain ⟨hOcal, K, hKn, hKset, hQ, hl, hcomm, hcent, hne'⟩ := hO
  have hmq : E3.mQuot V (conjSubgroup D.M g) ≤ 1 := hOcal.1.2.1
  have hVMg : ¬ V ≤ conjSubgroup D.M g := hOcal.2.1
  have hN : normalizer (V : Set G) = D.M := normalizer_eq_of_inCalV D hV
  have hNg : normalizer (conjSubgroup V g : Set G) = conjSubgroup D.M g := by
    rw [← CFSG.LocalAnalysis.WeakClosure81.conjSubgroup_normalizer V g, hN]
  have hU : V ⊓ conjSubgroup D.M g ≤ V₀ := by
    have hcent' : V ⊓ centralizer ((conjSubgroup V g ⊓ D.M : Subgroup G) : Set G) = V₀ := by
      rw [hcent, hbot, bot_sup_eq]
    rw [← hcent']
    refine le_inf inf_le_left ?_
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have huN : u ∈ normalizer (conjSubgroup V g : Set G) := hNg ▸ hu.2
    have hbN : b ∈ normalizer (V : Set G) := hN ▸ hb.2
    have hub : u * b * u⁻¹ ∈ conjSubgroup V g := (Subgroup.mem_normalizer_iff.1 huN b).1 hb.1
    have hbu : b * u⁻¹ * b⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 hbN u⁻¹).1 (V.inv_mem hu.1)
    have hmemV : u * b * u⁻¹ * b⁻¹ ∈ V := by
      have := V.mul_mem hu.1 hbu
      simpa [mul_assoc] using this
    have hmemVg : u * b * u⁻¹ * b⁻¹ ∈ conjSubgroup V g := by
      have := (conjSubgroup V g).mul_mem hub ((conjSubgroup V g).inv_mem hb.1)
      simpa [mul_assoc] using this
    have h1 : u * b * u⁻¹ * b⁻¹ = 1 :=
      Subgroup.mem_bot.1 (by rw [← hbot]; exact Subgroup.mem_inf.2 ⟨hmemV, hmemVg⟩)
    have hcomm' : b * u = u * b := by
      have h : (u * b) * (b * u)⁻¹ = 1 := by
        rw [mul_inv_rev]
        simpa [mul_assoc] using h1
      exact (mul_inv_eq_one.mp h).symm
    exact hcomm'
  have hU2 : IsPGroup 2 V := CFSG.Open.IsElemAbelian.isPGroup hV.2.2.2
  have hmqU : E3.mQuot V (V ⊓ conjSubgroup D.M g) ≤ 1 := by
    rw [CFSG.LocalAnalysis.WeakClosure81.mQuot_inf_left]
    exact hmq
  have hUne : V ⊓ conjSubgroup D.M g ≠ V := fun h =>
    hVMg ((le_of_eq h.symm).trans inf_le_right)
  have hUV : V ⊓ conjSubgroup D.M g ≤ V := inf_le_left
  have hmq_ne : E3.mQuot V (V ⊓ conjSubgroup D.M g) ≠ 0 := fun h0 =>
    hUne ((E3.mQuot_eq_zero_iff hU2 hUV).1 h0)
  have hmq1 : E3.mQuot V (V ⊓ conjSubgroup D.M g) = 1 :=
    Nat.le_antisymm hmqU (Nat.one_le_iff_ne_zero.mpr hmq_ne)
  have hcard : Nat.card ↥V = 2 * Nat.card ↥(V ⊓ conjSubgroup D.M g) := by
    have h := E3.card_eq_two_pow_mul hU2 hUV
    rw [hmq1] at h
    simpa using h
  have hrel : (V ⊓ conjSubgroup D.M g).relIndex V = 2 := by
    have h := Subgroup.relIndex_mul_card (H := V ⊓ conjSubgroup D.M g) (K := V)
    rw [inf_eq_left.2 hUV] at h
    rw [hcard] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(V ⊓ conjSubgroup D.M g))) h
  rcases CFSG.LocalAnalysis.GorensteinLyons.NonfusedCore.eq_or_eq_of_relIndex_eq_two
    hU hle hrel with h | h
  · exact hne' (by rw [hbot, bot_sup_eq, h])
  · exact hne h

theorem s16c1_not_centralizer_le_M {D : Data G} {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {g z : G} (hz : z ∈ V ⊓ conjSubgroup V g) (hVM : ¬ conjSubgroup V g ≤ D.M) :
    ¬ centralizer ({z} : Set G) ≤ D.M := by
  intro hC
  have hVg : IsMulCommutative ↥(conjSubgroup V g) :=
    (CFSG.LocalAnalysis.WeakClosure81.isElemAbelian_conjSubgroup' hV g).1
  have hsub : conjSubgroup V g ≤ Subgroup.centralizer (conjSubgroup V g : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hVg
  have hsing : ({z} : Set G) ⊆ (conjSubgroup V g : Set G) := by
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact hz.2
  exact hVM (hsub.trans ((Subgroup.centralizer_le hsing).trans hC))

theorem s16c1_exists_sylow_conj (D : Data G) (z : G) :
    ∃ k ∈ D.M, IsSylowIn 2 (D.T ⊓ centralizer ({k⁻¹ * z * k} : Set G))
      (D.M ⊓ centralizer ({k⁻¹ * z * k} : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : IsPGroup 2 (⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  obtain ⟨S, hS, -⟩ := exists_isSylowIn_ge 2
    (bot_le : (⊥ : Subgroup G) ≤ D.M ⊓ centralizer ({z} : Set G)) hbot
  obtain ⟨k, hkM, hk⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.exists_conj_le_of_isSylowOf D.sylowM
      (hS.le.trans inf_le_left) hS.isPGroup
  have hH' : D.M ⊓ centralizer ({k⁻¹ * z * k} : Set G) =
      conjSubgroup (D.M ⊓ centralizer ({z} : Set G)) k := by
    ext x
    rw [mem_conjSubgroup_iff, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hxM, hxc⟩
      refine ⟨D.M.mul_mem (D.M.mul_mem hkM hxM) (D.M.inv_mem hkM), fun y hy => ?_⟩
      rw [Set.mem_singleton_iff.1 hy]
      have := hxc (k⁻¹ * z * k) rfl
      calc z * (k * x * k⁻¹) = k * ((k⁻¹ * z * k) * x) * k⁻¹ := by group
        _ = k * (x * (k⁻¹ * z * k)) * k⁻¹ := by rw [this]
        _ = (k * x * k⁻¹) * z := by group
    · rintro ⟨hxM, hxc⟩
      refine ⟨?_, fun y hy => ?_⟩
      · have := D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hkM) hxM) hkM
        simpa [mul_assoc] using this
      · rw [Set.mem_singleton_iff.1 hy]
        have := hxc z rfl
        calc (k⁻¹ * z * k) * x = k⁻¹ * (z * (k * x * k⁻¹)) * k := by group
          _ = k⁻¹ * ((k * x * k⁻¹) * z) * k := by rw [this]
          _ = x * (k⁻¹ * z * k) := by group
  have hS'H' : IsSylowIn 2 (conjSubgroup S k)
      (conjSubgroup (D.M ⊓ centralizer ({z} : Set G)) k) :=
    isSylowIn_of_card_eq (E3.conjSubgroup_mono_left k hS.le)
      (by rw [E3.card_conjSubgroup, E3.card_conjSubgroup]; exact hS.card_eq)
  have hS'T : conjSubgroup S k ≤ D.T := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have := hk _ hx
    simpa [mul_assoc] using this
  have hS'P : conjSubgroup S k ≤ D.T ⊓ centralizer ({k⁻¹ * z * k} : Set G) := by
    intro x hx
    refine Subgroup.mem_inf.2 ⟨hS'T hx, ?_⟩
    have hx' : x ∈ D.M ⊓ centralizer ({k⁻¹ * z * k} : Set G) := by
      rw [hH']
      exact hS'H'.le hx
    exact (Subgroup.mem_inf.1 hx').2
  refine ⟨k, hkM, ?_⟩
  refine ⟨inf_le_inf_right _ D.sylowM.le, D.sylowM.isPGroup.to_le inf_le_left, ?_⟩
  rw [hH']
  intro hdvd
  exact hS'H'.not_dvd_relIndex (hdvd.trans (Subgroup.relIndex_dvd_of_le_left _ hS'P))

theorem s16c1_exists_pick (D : Data G) (h45 : R16_45 D) (hO1 : R16_47_O1_ne D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_1 D V₀ V hV L) (hL : L ∈ calC D.M) (hU4 : IsU4 (Bar2 L) 1) :
    ∃ x : IntMod V hV, Setup1645 D V hV x ∧ Chosen1647 D V₀ V x.val := by
  have hP := hS.setting.hyp151.hyp125.pairFacts
  have hVc : InCalV D.M V := hyp123_inCalV hS.setting.hyp151.hyp125.1
  obtain ⟨X, hX⟩ := hO1 V₀ V L hV hS hc hL hU4
  have hXs : X ∈ calOStar 1 D.M V₀ V := by
    rw [← h45 V₀ V L hV hS hc]
    exact hX
  obtain ⟨g, -, hg⟩ := hXs
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (s16c1_inter_ne_bot D hVc hP.le (s16c1_ne_V_of_sect16 hS) hg)
  have hz : (a : G) ∈ V ⊓ conjSubgroup V g := a.2
  have hz1 : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
  obtain ⟨k, hkM, hSyl⟩ := s16c1_exists_sylow_conj D (a : G)
  have hkV : k ∈ normalizer (V : Set G) := hP.le_normalizer hkM
  have hkV₀ : k ∈ normalizer (V₀ : Set G) := hP.le_normalizer₀ hkM
  have hz'V : k⁻¹ * (a : G) * k ∈ V := (Subgroup.mem_normalizer_iff''.1 hkV (a : G)).1 hz.1
  have hgk : InCalOStar 1 D.M V₀ V (g * k) := s16c1_inCalOStar_mul hkM hkV hkV₀ hg
  have hz'g : k⁻¹ * (a : G) * k ∈ conjSubgroup V (g * k) := by
    rw [mem_conjSubgroup_iff]
    have e : g * k * (k⁻¹ * (a : G) * k) * (g * k)⁻¹ = g * (a : G) * g⁻¹ := by group
    rw [e]
    exact (mem_conjSubgroup_iff.1 hz.2)
  refine ⟨IntMod.mk hV ⟨k⁻¹ * (a : G) * k, hz'V⟩, ⟨?_, ?_, hSyl⟩,
    ⟨g * k, hgk, Subgroup.mem_inf.2 ⟨hz'V, hz'g⟩⟩⟩
  · intro h1
    apply hz1
    have h1' : k⁻¹ * (a : G) * k = 1 := h1
    have e : (a : G) = k * (k⁻¹ * (a : G) * k) * k⁻¹ := by group
    rw [e, h1']
    group
  · exact s16c1_not_centralizer_le_M hV (z := k⁻¹ * (a : G) * k)
      (Subgroup.mem_inf.2 ⟨hz'V, hz'g⟩) hgk.1.1.1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

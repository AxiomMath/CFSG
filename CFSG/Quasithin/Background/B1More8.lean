module

public import CFSG.Quasithin.Background.CentSecConj
public import CFSG.Quasithin.Background.A1aFStar
public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.Quasithin.Background.B1Restrict

public section

namespace CFSG.Quasithin

open CFSG.Open

section Conj

variable {V : Type*} [CommGroup V]

theorem conj_mem_centSub {U : Subgroup V} {g c : MulAut V} (hg : g ∈ stabSub U)
    (hc : c ∈ centSub U) : g * c * g⁻¹ ∈ centSub U := by
  intro u hu
  have h1 : g⁻¹ u ∈ U := ((stabSub U).inv_mem hg u).2 hu
  change g (c (g⁻¹ u)) = u
  rw [hc _ h1]
  simp

theorem conj_mem_centQuot {W : Subgroup V} {g c : MulAut V} (hg : g ∈ stabSub W)
    (hc : c ∈ centQuot W) : g * c * g⁻¹ ∈ centQuot W := by
  intro v
  have h1 := hc (g⁻¹ v)
  have h2 := (hg _).2 h1
  have h3 : g (c (g⁻¹ v) * (g⁻¹ v)⁻¹) = (g * c * g⁻¹) v * v⁻¹ := by
    rw [map_mul, map_inv]
    simp
  rw [← h3]
  exact h2

theorem conj_mem_centSec {W U : Subgroup V} {g c : MulAut V} (hgW : g ∈ stabSub W)
    (hgU : g ∈ stabSub U) (hc : c ∈ centSec W U) : g * c * g⁻¹ ∈ centSec W U :=
  CFSG.Quasithin.StabLat.conj_mem_centSec hgW hgU hc

end Conj

namespace B1More

variable {Ω : Type*} [Group Ω] [Finite Ω]

theorem normal_le_center_genFitting {G N : Subgroup Ω} (hNG : N ≤ G)
    (hN : ∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hL : CFSG.IsQuasisimple ↥(quasithinGenFitting G)) (hNL : ¬ quasithinGenFitting G ≤ N) :
    N ≤ quasithinGenFitting G ∧ N ≤ Subgroup.centralizer (quasithinGenFitting G : Set Ω) := by
  set L := quasithinGenFitting G with hLdef
  have hLo : CFSG.Open.IsQuasisimple ↥L := ⟨Group.isPerfect_def.mp hL.1, hL.2.1⟩
  have hLG : L ≤ G := quasithinGenFitting_le G
  have hLn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L := fun g hg l hl =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_quasithinGenFitting G hg) l).mp hl
  have hCL : G ⊓ Subgroup.centralizer (L : Set Ω) ≤ L := centralizer_quasithinGenFitting_le G
  have hcentral : N ⊓ L ≤ Subgroup.centralizer (L : Set Ω) := by
    have hnorm : ((N ⊓ L).subgroupOf L).Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      refine ⟨?_, ?_⟩
      · have := hN (g : Ω) (hLG g.2) x hx.1
        simpa using this
      · exact L.mul_mem (L.mul_mem g.2 hx.2) (L.inv_mem g.2)
    have hne : (N ⊓ L).subgroupOf L ≠ ⊤ := by
      intro h
      apply hNL
      intro l hl
      have : (⟨l, hl⟩ : L) ∈ (N ⊓ L).subgroupOf L := by rw [h]; trivial
      rw [Subgroup.mem_subgroupOf] at this
      exact this.1
    have hc := CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hLo _ hne
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hx' : (⟨x, hx.2⟩ : L) ∈ (N ⊓ L).subgroupOf L := hx
    have := Subgroup.mem_center_iff.mp (hc hx') ⟨l, hl⟩
    exact congrArg Subtype.val this
  have hcomm : ⁅N, L⁆ ≤ N ⊓ L := by
    rw [Subgroup.commutator_le]
    intro n hn l hl
    refine ⟨?_, ?_⟩
    · have h1 := hN l (hLG hl) n⁻¹ (N.inv_mem hn)
      have : n * l * n⁻¹ * l⁻¹ = n * (l * n⁻¹ * l⁻¹) := by simp [mul_assoc]
      show n * l * n⁻¹ * l⁻¹ ∈ N
      rw [this]
      exact N.mul_mem hn h1
    · have h1 := hLn n (hNG hn) l hl
      show n * l * n⁻¹ * l⁻¹ ∈ L
      exact L.mul_mem h1 (L.inv_mem hl)
  have h1 : ⁅⁅N, L⁆, L⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hcomm.trans hcentral)
  have h2 : ⁅⁅L, N⁆, L⁆ = ⊥ := by rw [Subgroup.commutator_comm L N]; exact h1
  have h3 : ⁅⁅L, L⁆, N⁆ = ⊥ := three_subgroup_lemma h2 h1
  have hperf : Group.IsPerfect ↥L := hL.1
  rw [Subgroup.commutator_eq_self] at h3
  have h4 : N ≤ Subgroup.centralizer (L : Set Ω) := by
    rw [Subgroup.commutator_comm] at h3
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  exact ⟨fun x hx => hCL ⟨hNG hx, h4 hx⟩, h4⟩

theorem eq_bot_of_le_center_genFitting {G Y : Subgroup Ω}
    (hO2 : pCoreOf 2 G = ⊥) (hY2 : IsPGroup 2 Y)
    (hYL : Y ≤ quasithinGenFitting G)
    (hYc : Y ≤ Subgroup.centralizer (quasithinGenFitting G : Set Ω)) : Y = ⊥ := by
  set L := quasithinGenFitting G with hLdef
  have hLG : L ≤ G := quasithinGenFitting_le G
  have hLn : G ≤ Subgroup.normalizer (L : Set Ω) := le_normalizer_quasithinGenFitting G
  have hLY : L ≤ Subgroup.normalizer (Y : Set Ω) := fun l hl =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (hYc hy) l hl).symm)
  have h1 : Y ≤ pCoreOf 2 L := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hYL hLY hY2
  have h2 : pCoreOf 2 L ≤ pCoreOf 2 G :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLG)
      (hLn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  rw [hO2] at h2
  exact le_bot_iff.mp (h1.trans h2)

end B1More

section Elem

variable {V : Type*} [CommGroup V]

theorem isElemAbelian2_autSub {A : Subgroup (MulAut V)} (W : Subgroup V) (hA : IsElemAbelian2 A) :
    IsElemAbelian2 (autSub A W) := by
  refine ⟨?_, ?_⟩
  · intro φ hφ ψ hψ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    obtain ⟨h, hh, rfl⟩ := mem_autSub.mp hψ
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hA.1 _ hg _ hh)
  · intro φ hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    rw [← map_pow]
    have : g ^ 2 = 1 := Subtype.ext (hA.2 _ hg)
    rw [this, map_one]

theorem isElemAbelian2_autQuot {A : Subgroup (MulAut V)} (U : Subgroup V)
    (hA : IsElemAbelian2 A) : IsElemAbelian2 (autQuot A U) := by
  refine ⟨?_, ?_⟩
  · intro φ hφ ψ hψ
    obtain ⟨g, hg, rfl⟩ := mem_autQuot.mp hφ
    obtain ⟨h, hh, rfl⟩ := mem_autQuot.mp hψ
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hA.1 _ hg _ hh)
  · intro φ hφ
    obtain ⟨g, hg, rfl⟩ := mem_autQuot.mp hφ
    rw [← map_pow]
    have : g ^ 2 = 1 := Subtype.ext (hA.2 _ hg)
    rw [this, map_one]

theorem isElemAbelian2_autSec {A : Subgroup (MulAut V)} (W U : Subgroup V)
    (hA : IsElemAbelian2 A) : IsElemAbelian2 (autSec A W U) :=
  isElemAbelian2_autQuot _ (isElemAbelian2_autSub W hA)

theorem sq_eq_one_quotient (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V) :
    ∀ x : V ⧸ U, x ^ 2 = 1 := by
  intro x
  induction x using QuotientGroup.induction_on with
  | H v => rw [← QuotientGroup.mk_pow, hV v]; rfl

theorem sq_eq_one_sec (hV : ∀ v : V, v ^ 2 = 1) (W U : Subgroup V) :
    ∀ x : Sec W U, x ^ 2 = 1 :=
  sq_eq_one_quotient (B1.sq_eq_one_sub hV W) _

theorem not_isStrongFFModule_of_one_le_qOf [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X : Subgroup (MulAut V)} (hq : (1 : WithTop ℚ) ≤ qOf X) : ¬ IsStrongFFModule X := by
  intro h
  obtain ⟨A, hA2, hlt⟩ := (isStrongFFModule_iff hV).1 h
  obtain ⟨B, -, hB, hrB⟩ := B1_4_4_lt hV hA2 hlt
  have := rAV_eq_one_of_one_le_qOf hV hq hB
  rw [this] at hrB
  exact lt_irrefl _ hrB

end Elem

section B158

variable {V : Type*} [CommGroup V] [Finite V]

theorem B1_5_8 (hV : ∀ v : V, v ^ 2 = 1) {G A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender G A) {W U : Subgroup V} (hUW : U ≤ W) (hGW : G ≤ stabSub W)
    (hGU : G ≤ stabSub U) (hL : CFSG.IsQuasisimple ↥(quasithinGenFitting G))
    (hO2 : pCoreOf 2 G = ⊥) (hS : ¬ commSub W (quasithinGenFitting G) ≤ U) :
    A ⊓ centSec W U = ⊥ ∧
      (∃ B, B ≤ autSec A W U ∧ IsFFStarOffender (autSec G W U) B) ∧
      (qOf (autSec G W U) = 1 →
        IsFFStarOffender (autSec G W U) (autSec A W U) ∧
          A ⊔ quasithinGenFitting G ≤ centSub U ⊓ centQuot W ∧ W ⊔ fixV A = ⊤) := by
  set L := quasithinGenFitting G with hLdef
  have hAG : A ≤ G := hA.1
  have hAne : A ≠ ⊥ := hA.2.1
  have hAel : IsElemAbelian2 A := hA.2.2.1
  have hApg : IsPGroup 2 A := hAel.isPGroup
  have hAW : A ≤ stabSub W := hAG.trans hGW
  have hAU : A ≤ stabSub U := hAG.trans hGU
  have hS2 : ∀ x : Sec W U, x ^ 2 = 1 := sq_eq_one_sec hV W U
  have hC : G ⊓ centSec W U ≤ L ∧ G ⊓ centSec W U ≤ Subgroup.centralizer (L : Set (MulAut V)) := by
    refine B1More.normal_le_center_genFitting inf_le_left ?_ hL ?_
    · intro g hg n hn
      exact ⟨G.mul_mem (G.mul_mem hg hn.1) (G.inv_mem hg),
        conj_mem_centSec (hGW hg) (hGU hg) hn.2⟩
    · intro hLN
      apply hS
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, w, hw, rfl⟩
      exact (hLN hx).2.2 w hw
  have hfaith : A ⊓ centSec W U = ⊥ := by
    refine B1More.eq_bot_of_le_center_genFitting hO2 (hApg.to_le inf_le_left) ?_ ?_
    · exact fun x hx => hC.1 ⟨hAG hx.1, hx.2⟩
    · exact fun x hx => hC.2 ⟨hAG hx.1, hx.2⟩
  have hcard : Nat.card (autSec A W U) = Nat.card A := by
    have := card_autSec_mul hAW hAU
    rw [hfaith, Subgroup.card_bot, mul_one] at this
    exact this
  have hA'2 : IsA2 (autSec G W U) (autSec A W U) := by
    refine ⟨autSec_mono hAG W U, ?_, isElemAbelian2_autSec W U hAel⟩
    intro h
    have h1 : Nat.card (autSec A W U) = 1 := by rw [h]; exact Subgroup.card_bot
    rw [hcard] at h1
    exact hAne (Subgroup.card_eq_one.mp h1)
  have hr1 : rAV (autSec A W U) ≤ 1 := by
    refine (rAV_le_one_iff hS2 hA'2).2 ?_
    have := (section_numerics hA hUW hAW).2.2
    rw [hcard]
    exact this
  refine ⟨hfaith, ?_, fun hq => ?_⟩
  · obtain ⟨B, hBA, hB, -⟩ := B1_4_4_le hS2 hA'2 hr1
    exact ⟨B, hBA, hB⟩
  · have hq' : (1 : WithTop ℚ) ≤ qOf (autSec G W U) := hq ▸ le_rfl
    have hns := not_isStrongFFModule_of_one_le_qOf hS2 hq'
    have hr : rAV (autSec A W U) = 1 := by
      refine le_antisymm hr1 (not_lt.1 fun hlt => hns ?_)
      exact (isStrongFFModule_iff hS2).2 ⟨_, hA'2, hlt⟩
    have hP : IsFFStarOffender (autSec G W U) (autSec A W U) := by
      have := B1_4_6 hS2 hns
      have hmem : autSec A W U ∈ {A | IsA2 (autSec G W U) A ∧ rAV A = 1} := ⟨hA'2, hr⟩
      rw [← this] at hmem
      exact hmem
    have hEq : Nat.card (Sec W U) = Nat.card A * Nat.card (fixV (autSec A W U)) := by
      have := (rAV_eq_one_iff hS2 hA'2).1 hr
      rw [hcard] at this
      exact this
    obtain ⟨hUfix, hWsup⟩ := section_equality hA hUW hAW hEq
    have hAcU : A ≤ centSub U := fun a ha u hu => hUfix hu a ha
    have hAcW : A ≤ centQuot W := by
      intro a ha v
      have hv : v ∈ W ⊔ fixV A := by rw [hWsup]; trivial
      obtain ⟨w, hw, c, hc, rfl⟩ := Subgroup.mem_sup.1 hv
      have : a (w * c) * (w * c)⁻¹ = a w * w⁻¹ := by
        rw [map_mul, hc a ha]
        group
      rw [this]
      exact W.mul_mem ((hAW ha w).2 hw) (W.inv_mem hw)
    have hAC : A ≤ G ⊓ (centSub U ⊓ centQuot W) := le_inf hAG (le_inf hAcU hAcW)
    have hLC : L ≤ G ⊓ (centSub U ⊓ centQuot W) := by
      by_contra hLC
      obtain ⟨h1, h2⟩ := B1More.normal_le_center_genFitting
        (G := G) (N := G ⊓ (centSub U ⊓ centQuot W)) inf_le_left
        (fun g hg n hn => ⟨G.mul_mem (G.mul_mem hg hn.1) (G.inv_mem hg),
          conj_mem_centSub (hGU hg) hn.2.1, conj_mem_centQuot (hGW hg) hn.2.2⟩) hL hLC
      exact hAne (B1More.eq_bot_of_le_center_genFitting hO2 hApg (hAC.trans h1) (hAC.trans h2))
    exact ⟨hP, sup_le (hAC.trans inf_le_right) (hLC.trans inf_le_right), hWsup⟩

end B158

end CFSG.Quasithin

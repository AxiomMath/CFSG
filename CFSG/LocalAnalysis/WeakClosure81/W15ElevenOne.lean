module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenSix
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenCop
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenP1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_cSub15_iff {M V₀ V U H P : Subgroup G} {x : G} :
    x ∈ cSub15 M V₀ V U H P ↔
      x ∈ tSub15 M V₀ V U P ∧ x ∈ centralizer (kHull15 V₀ H : Set G) := by
  unfold cSub15
  exact Subgroup.mem_inf

theorem cSub15_le_tSub15 (M V₀ V U H P : Subgroup G) :
    cSub15 M V₀ V U H P ≤ tSub15 M V₀ V U P :=
  fun _ hx => (mem_cSub15_iff.1 hx).1

theorem cSub15_le_centralizer (M V₀ V U H P : Subgroup G) :
    cSub15 M V₀ V U H P ≤ centralizer (kHull15 V₀ H : Set G) :=
  fun _ hx => (mem_cSub15_iff.1 hx).2

namespace Cfg1511

variable {M V₀ V U S H P Q₀ X : Subgroup G} {p : ℕ} {v : G}

private theorem conj_mem_cSub15 (c : Cfg1511 M V₀ V U S H P Q₀ p) {t y : G}
    (ht : t ∈ tSub15 M V₀ V U P) (hy : y ∈ cSub15 M V₀ V U H P) :
    t * y * t⁻¹ ∈ cSub15 M V₀ V U H P := by
  have hyT : y ∈ tSub15 M V₀ V U P := (mem_cSub15_iff.1 hy).1
  have hyC : y ∈ centralizer (kHull15 V₀ H : Set G) := (mem_cSub15_iff.1 hy).2
  refine mem_cSub15_iff.2 ⟨?_, ?_⟩
  · simpa [mul_assoc] using
      (tSub15 M V₀ V U P).mul_mem ht
        ((tSub15 M V₀ V U P).mul_mem hyT ((tSub15 M V₀ V U P).inv_mem ht))
  · rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : t⁻¹ * k * t ∈ kHull15 V₀ H := by
      have := (Subgroup.mem_normalizer_iff.1
        (c.tSub15_le_normalizer_kHull15 ((tSub15 M V₀ V U P).inv_mem ht)) k).1 hk
      simpa using this
    have hcomm : (t⁻¹ * k * t) * y = y * (t⁻¹ * k * t) :=
      Subgroup.mem_centralizer_iff.1 hyC (t⁻¹ * k * t) hk'
    calc k * (t * y * t⁻¹) = t * ((t⁻¹ * k * t) * y) * t⁻¹ := by group
      _ = t * (y * (t⁻¹ * k * t)) * t⁻¹ := by rw [hcomm]
      _ = (t * y * t⁻¹) * k := by group

private theorem b15_le_normalizer_of_conj_mem (S C : Subgroup G)
    (h : ∀ g ∈ S, ∀ y ∈ C, g * y * g⁻¹ ∈ C) : S ≤ normalizer (C : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact h g hg y
  · intro hy
    have h2 := h g⁻¹ (S.inv_mem hg) (g * y * g⁻¹) hy
    have h3 : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rwa [h3] at h2

theorem le_normalizer_cSub15 (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    kHull15 V₀ H ⊔ tSub15 M V₀ V U P ≤ normalizer (cSub15 M V₀ V U H P : Set G) := by
  refine sup_le ?_ ?_
  · refine b15_le_normalizer_of_conj_mem _ _ fun k hk y hy => ?_
    have hcomm : k * y = y * k :=
      Subgroup.mem_centralizer_iff.1 (mem_cSub15_iff.1 hy).2 k hk
    have hky : k * y * k⁻¹ = y := by rw [hcomm]; group
    rw [hky]
    exact hy
  · exact b15_le_normalizer_of_conj_mem _ _ fun t ht y hy => conj_mem_cSub15 c ht hy

theorem cSub15_le_qSub15 (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    cSub15 M V₀ V U H P ≤ qSub15 M V₀ V U H P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold qSub15
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
  · exact (cSub15_le_tSub15 M V₀ V U H P).trans le_sup_right
  · exact le_normalizer_cSub15 c
  · exact c.hyp.sylow.isPGroup.to_le
      ((cSub15_le_tSub15 M V₀ V U H P).trans (tSub15_le_P M V₀ V U P))

end Cfg1511

namespace XData15

variable {M V₀ V U S H P Q₀ X : Subgroup G} {p : ℕ} {v : G}

theorem commutator_mem_iHull15
    (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v) {x q : G} (hx : x ∈ X)
    (hq : q ∈ qSub15 M V₀ V U H P) : ⁅x, q⁆ ∈ iHull15 V₀ U H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← c.qSub15_inf_kHull15]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have hxN : x ∈ normalizer (qSub15 M V₀ V U H P : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2
        (kHull15 V₀ H ⊔ tSub15 M V₀ V U P)
        (Subgroup.mem_sup_left (hX.le_kHull15 hx))
    have hxq : x * q * x⁻¹ ∈ qSub15 M V₀ V U H P :=
      (Subgroup.mem_normalizer_iff.1 hxN q).1 hq
    rw [commutatorElement_def]
    simpa [mul_assoc] using
      (qSub15 M V₀ V U H P).mul_mem hxq ((qSub15 M V₀ V U H P).inv_mem hq)
  · have hqT : q ∈ tSub15 M V₀ V U P := c.qSub15_le_tSub15 hq
    have hqN : q ∈ normalizer (kHull15 V₀ H : Set G) := c.tSub15_le_normalizer_kHull15 hqT
    have hqx : q * x⁻¹ * q⁻¹ ∈ kHull15 V₀ H :=
      (Subgroup.mem_normalizer_iff.1 hqN x⁻¹).1 ((kHull15 V₀ H).inv_mem (hX.le_kHull15 hx))
    rw [commutatorElement_def]
    simpa [mul_assoc] using (kHull15 V₀ H).mul_mem (hX.le_kHull15 hx) hqx

theorem inf_centralizer_le_centralizer_iHull15
    (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v) :
    tSub15 M V₀ V U P ⊓ centralizer (X : Set G) ≤ centralizer (iHull15 V₀ U H : Set G) := by
  intro y hy
  have hyT : y ∈ tSub15 M V₀ V U P := (Subgroup.mem_inf.1 hy).1
  have hyX : y ∈ centralizer (X : Set G) := (Subgroup.mem_inf.1 hy).2
  have hle : iHull15 V₀ U H ≤ centralizer ({y} : Set G) := by
    rw [← hX.conjClosure_eq c]
    refine CFSG.Quasithin.conjClosure_le fun x hx z hz => ?_
    have hxmem : x ∈ centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact (Subgroup.mem_centralizer_iff.1 hyX x hx).symm
    have hzmem : z ∈ centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact (Subgroup.mem_centralizer_iff.1
        (tSub15_le_centralizer M V₀ V U P hyT) z hz).symm
    exact (centralizer ({y} : Set G)).mul_mem
      ((centralizer ({y} : Set G)).mul_mem hxmem hzmem)
      ((centralizer ({y} : Set G)).inv_mem hxmem)
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact (Subgroup.mem_centralizer_iff.1 (hle hh) y (Set.mem_singleton y)).symm

theorem tSub15_inf_centralizer_le
    (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v) :
    tSub15 M V₀ V U P ⊓ centralizer (X : Set G) ≤ cSub15 M V₀ V U H P := by
  intro y hy
  have hyT : y ∈ tSub15 M V₀ V U P := (Subgroup.mem_inf.1 hy).1
  have hyX : y ∈ centralizer (X : Set G) := (Subgroup.mem_inf.1 hy).2
  have hcomm_v : y * v = v * y := by
    have hyCT : y ∈ F11.CTilde M V₀ V := tSub15_le_cTilde M V₀ V U P hyT
    have hvV : v ∈ V := c.cex.hyp.h6.le hX.mem
    have hmemV₀ : y * v * y⁻¹ * v⁻¹ ∈ V₀ :=
      (FourteenTwo.mem_cTilde_iff_comm.1 hyCT).2.2 v hvV
    have hmem2 : v * y⁻¹ * v⁻¹ ∈ centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hvN : v⁻¹ ∈ normalizer (X : Set G) :=
        (Subgroup.normalizer (X : Set G)).inv_mem hX.normalizes
      have hvx : v⁻¹ * x * v ∈ X := by
        have := (Subgroup.mem_normalizer_iff.1 hvN x).1 hx
        simpa using this
      have hyinv : y⁻¹ ∈ centralizer (X : Set G) := (centralizer (X : Set G)).inv_mem hyX
      have hcomm : (v⁻¹ * x * v) * y⁻¹ = y⁻¹ * (v⁻¹ * x * v) :=
        Subgroup.mem_centralizer_iff.1 hyinv (v⁻¹ * x * v) hvx
      calc x * (v * y⁻¹ * v⁻¹)
          = (v * (v⁻¹ * x * v) * v⁻¹) * (v * y⁻¹ * v⁻¹) := by group
        _ = v * ((v⁻¹ * x * v) * y⁻¹) * v⁻¹ := by group
        _ = v * (y⁻¹ * (v⁻¹ * x * v)) * v⁻¹ := by rw [hcomm]
        _ = (v * y⁻¹ * v⁻¹) * x := by group
    have hmemC : y * v * y⁻¹ * v⁻¹ ∈ centralizer (X : Set G) := by
      have := (centralizer (X : Set G)).mul_mem hyX hmem2
      simpa [mul_assoc] using this
    have hmem : y * v * y⁻¹ * v⁻¹ ∈ V₀ ⊓ centralizer (X : Set G) := ⟨hmemV₀, hmemC⟩
    rw [hX.inf_centralizer_X c] at hmem
    have h1 : ⁅y, v⁆ = 1 := by
      rw [commutatorElement_def]
      exact Subgroup.mem_bot.1 hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  refine mem_cSub15_iff.2 ⟨hyT, ?_⟩
  have hV0C : V₀ ≤ centralizer ({y} : Set G) := by
    have hvC : v ∈ centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact hcomm_v
    have hV1C : v1Sub15 V₀ U ≤ centralizer ({y} : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact (Subgroup.mem_centralizer_iff.1
        (tSub15_le_centralizer M V₀ V U P hyT) z hz).symm
    exact (hX.le_zpowers_sup c).trans (sup_le (Subgroup.zpowers_le.2 hvC) hV1C)
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨x, hx, i, hi, w, hw, ha'⟩ := c.exists_mul_mul_of_mem_kHull15 hX.sylow ha
  rw [ha']
  have hXi : y ∈ centralizer (iHull15 V₀ U H : Set G) :=
    inf_centralizer_le_centralizer_iHull15 c hX ⟨hyT, hyX⟩
  have hx' : x ∈ centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (Subgroup.mem_centralizer_iff.1 hyX x hx).symm
  have hi' : i ∈ centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (Subgroup.mem_centralizer_iff.1 hXi i hi).symm
  have hw' : w ∈ centralizer ({y} : Set G) := hV0C hw
  have hprod : x * i * w ∈ centralizer ({y} : Set G) :=
    (centralizer ({y} : Set G)).mul_mem
      ((centralizer ({y} : Set G)).mul_mem hx' hi') hw'
  exact (Subgroup.mem_centralizer_iff.1 hprod y (Set.mem_singleton y)).symm

end XData15

namespace Cfg1511

variable {M V₀ V U S H P Q₀ X : Subgroup G} {p : ℕ} {v : G}

theorem qSub15_eq_sup (c : Cfg1511 M V₀ V U S H P Q₀ p)
    (hX : XData15 V₀ U H Q₀ p X v) :
    qSub15 M V₀ V U H P = iHull15 V₀ U H ⊔ cSub15 M V₀ V U H P := by
  haveI : Fact p.Prime := ⟨c.prime⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (sup_le c.iHull15_le_qSub15 c.cSub15_le_qSub15)
  have hI : IsPGroup 2 (iHull15 V₀ U H) :=
    c.hyp.sylow.isPGroup.to_le (c.hyp.iHull15_le_P c.cex)
  have hXI : X ≤ normalizer (iHull15 V₀ U H : Set G) :=
    hX.le_kHull15.trans (c.hyp.kHull15_le.trans (Hyp1510.le_normalizer_iHull15 V₀ U H))
  have hQI : qSub15 M V₀ V U H P ≤ normalizer (iHull15 V₀ U H : Set G) :=
    c.qSub15_le_tSub15.trans (c.tSub15_le_H.trans (Hyp1510.le_normalizer_iHull15 V₀ U H))
  have hle := le_inf_centralizer_sup_of_comm_mem c.p_ne_two
    (Q := qSub15 M V₀ V U H P) (I := iHull15 V₀ U H) (X := X)
    hX.isPGroup hI c.iHull15_le_qSub15 hXI hQI
    (fun x hx q hq => hX.commutator_mem_iHull15 c hx hq)
  have hsub : qSub15 M V₀ V U H P ⊓ centralizer (X : Set G) ≤ cSub15 M V₀ V U H P := by
    intro y hy
    exact hX.tSub15_inf_centralizer_le c
      ⟨c.qSub15_le_tSub15 (Subgroup.mem_inf.1 hy).1, (Subgroup.mem_inf.1 hy).2⟩
  have hle' : qSub15 M V₀ V U H P ≤ cSub15 M V₀ V U H P ⊔ iHull15 V₀ U H :=
    hle.trans (sup_le (hsub.trans le_sup_left) le_sup_right)
  rwa [sup_comm] at hle'

theorem iHull15_inf_cSub15 (hX : XData15 V₀ U H Q₀ p X v) :
    iHull15 V₀ U H ⊓ cSub15 M V₀ V U H P = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyI, hyC⟩ := Subgroup.mem_inf.1 hy
  have hyX : y ∈ centralizer (X : Set G) :=
    Subgroup.centralizer_le hX.le_kHull15 (mem_cSub15_iff.1 hyC).2
  have hmem : y ∈ iHull15 V₀ U H ⊓ centralizer (X : Set G) := ⟨hyI, hyX⟩
  rw [hX.cent] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem kHull15_inf_cSub15 (c : Cfg1511 M V₀ V U S H P Q₀ p)
    (hX : XData15 V₀ U H Q₀ p X v) :
    kHull15 V₀ H ⊓ cSub15 M V₀ V U H P = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyK, hyC⟩ := Subgroup.mem_inf.1 hy
  have hyQ : y ∈ qSub15 M V₀ V U H P := c.cSub15_le_qSub15 hyC
  have hyQI : y ∈ qSub15 M V₀ V U H P ⊓ kHull15 V₀ H := ⟨hyQ, hyK⟩
  rw [c.qSub15_inf_kHull15] at hyQI
  have hmem : y ∈ iHull15 V₀ U H ⊓ cSub15 M V₀ V U H P := ⟨hyQI, hyC⟩
  rw [iHull15_inf_cSub15 hX] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem cSub15_le_centralizer_V (c : Cfg1511 M V₀ V U S H P Q₀ p)
    (hX : XData15 V₀ U H Q₀ p X v) :
    cSub15 M V₀ V U H P ≤ centralizer (V : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hyT : y ∈ tSub15 M V₀ V U P := (mem_cSub15_iff.1 hy).1
  have hwT : w ∈ tSub15 M V₀ V U P := c.V_le_tSub15 hw
  have hconj : w * y⁻¹ * w⁻¹ ∈ cSub15 M V₀ V U H P :=
    conj_mem_cSub15 c hwT ((cSub15 M V₀ V U H P).inv_mem hy)
  have hcommC : ⁅y, w⁆ ∈ cSub15 M V₀ V U H P := by
    rw [commutatorElement_def]
    simpa [mul_assoc] using (cSub15 M V₀ V U H P).mul_mem hy hconj
  have hcommV₀ : ⁅y, w⁆ ∈ V₀ := by
    have hyCT : y ∈ F11.CTilde M V₀ V := tSub15_le_cTilde M V₀ V U P hyT
    have hm := (FourteenTwo.mem_cTilde_iff_comm.1 hyCT).2.2 w hw
    rw [commutatorElement_def]
    exact hm
  have hcommK : ⁅y, w⁆ ∈ centralizer (kHull15 V₀ H : Set G) := (mem_cSub15_iff.1 hcommC).2
  have hbot : ⁅y, w⁆ ∈ V₀ ⊓ centralizer (kHull15 V₀ H : Set G) := ⟨hcommV₀, hcommK⟩
  rw [hX.inf_centralizer_kHull15 c] at hbot
  have h1 : ⁅y, w⁆ = 1 := Subgroup.mem_bot.1 hbot
  exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

end Cfg1511

end CFSG.LocalAnalysis.WeakClosure81

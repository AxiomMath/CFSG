module

public import CFSG.RankThree.PartOne.K159.InnLayer
public import CFSG.RankThree.PartOne.K159.InnLayerComb
public import CFSG.RankThree.PartOne.S12.Sec1510FiveDefs
public import CFSG.RankThree.PartOne.S15K.RowFive
import CFSG.RankThree.PartOne.S10.PlaneTwoGroupLemmas

public section

namespace CFSG.RankThree.PartOne.K159

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S15K
open scoped commutatorElement

variable {G : Type} [Group G]

theorem perfect_le_sup_of_commute {I C Y₀ : Subgroup G} {e : G}
    (hIC : ∀ a ∈ I, ∀ b ∈ C, a * b = b * a) (heC : ∀ d ∈ C, e * d = d * e)
    (hY₀ : ∀ P : Subgroup G, P ≤ I ⊓ Subgroup.centralizer ({e} : Set G) →
      Group.IsPerfect ↥P → P ≤ Y₀)
    {Y : Subgroup G} (hYperf : Group.IsPerfect ↥Y) (hYIC : Y ≤ I ⊔ C)
    (hYe : Y ≤ Subgroup.centralizer ({e} : Set G)) : Y ≤ Y₀ ⊔ C := by
  classical
  let SY : Subgroup G :=
    { carrier := {i | i ∈ I ∧ ∃ d ∈ C, i * d ∈ Y}
      mul_mem' := by
        rintro a b ⟨haI, d₁, hd₁, h₁⟩ ⟨hbI, d₂, hd₂, h₂⟩
        refine ⟨I.mul_mem haI hbI, d₁ * d₂, C.mul_mem hd₁ hd₂, ?_⟩
        have h := hIC b hbI d₁ hd₁
        have : a * b * (d₁ * d₂) = (a * d₁) * (b * d₂) := by
          calc a * b * (d₁ * d₂) = a * (b * d₁) * d₂ := by group
            _ = a * (d₁ * b) * d₂ := by rw [h]
            _ = (a * d₁) * (b * d₂) := by group
        rw [this]
        exact Y.mul_mem h₁ h₂
      one_mem' := ⟨I.one_mem, 1, C.one_mem, by simp⟩
      inv_mem' := by
        rintro a ⟨haI, d, hd, h⟩
        refine ⟨I.inv_mem haI, d⁻¹, C.inv_mem hd, ?_⟩
        have h1 := hIC a haI d hd
        have : a⁻¹ * d⁻¹ = (a * d)⁻¹ := by
          calc a⁻¹ * d⁻¹ = (d * a)⁻¹ := by group
            _ = (a * d)⁻¹ := by rw [h1]
        rw [this]
        exact Y.inv_mem h }
  have hSYI : ∀ i ∈ SY, i ∈ I := fun i hi => hi.1
  have hSYe : ∀ i ∈ SY, i ∈ Subgroup.centralizer ({e} : Set G) := by
    rintro i ⟨hiI, d, hd, hid⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : (i * d) * e = e * (i * d) := Subgroup.mem_centralizer_singleton_iff.1 (hYe hid)
    have h2 := heC d hd
    have h3 : i * e * d = e * i * d := by
      calc i * e * d = i * (e * d) := by group
        _ = i * (d * e) := by rw [h2]
        _ = (i * d) * e := by group
        _ = e * (i * d) := h1
        _ = e * i * d := by group
    exact mul_right_cancel h3
  set P : Subgroup G := ⁅SY, SY⁆ with hP
  have hPSY : P ≤ SY := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact SY.mul_mem (SY.mul_mem (SY.mul_mem ha hb) (SY.inv_mem ha)) (SY.inv_mem hb)
  have hPI : ∀ x ∈ P, x ∈ I := fun x hx => hSYI x (hPSY hx)
  have hPC : ∀ x ∈ P, ∀ y ∈ C, x * y = y * x := fun x hx y hy => hIC x (hPI x hx) y hy
  have hYPC : Y ≤ P ⊔ C := by
    calc Y = ⁅Y, Y⁆ := ((Subgroup.isPerfect_iff).1 hYperf).symm
      _ ≤ P ⊔ C := by
        rw [Subgroup.commutator_def]
        refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨y₁, hy₁, y₂, hy₂, rfl⟩
        obtain ⟨i₁, hi₁, d₁, hd₁, h₁⟩ := PlaneCommuting.exists_mul_of_mem_sup hIC (hYIC hy₁)
        obtain ⟨i₂, hi₂, d₂, hd₂, h₂⟩ := PlaneCommuting.exists_mul_of_mem_sup hIC (hYIC hy₂)
        have hi₁S : i₁ ∈ SY := ⟨hi₁, d₁, hd₁, h₁ ▸ hy₁⟩
        have hi₂S : i₂ ∈ SY := ⟨hi₂, d₂, hd₂, h₂ ▸ hy₂⟩
        rw [h₁, h₂, PlaneCommuting.commutatorElement_mul_mul hIC ⟨i₁, hi₁⟩ ⟨i₂, hi₂⟩
          ⟨d₁, hd₁⟩ ⟨d₂, hd₂⟩]
        refine Subgroup.mul_mem_sup (Subgroup.commutator_mem_commutator hi₁S hi₂S) ?_
        rw [commutatorElement_def]
        exact C.mul_mem (C.mul_mem (C.mul_mem hd₁ hd₂) (C.inv_mem hd₁)) (C.inv_mem hd₂)
  have hPperf : Group.IsPerfect ↥P := by
    rw [Subgroup.isPerfect_iff]
    refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) ?_
    · rw [commutatorElement_def]
      exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)
    · refine Subgroup.commutator_le.2 fun i₁ hi₁ i₂ hi₂ => ?_
      obtain ⟨d₁, hd₁, hy₁⟩ := hi₁.2
      obtain ⟨d₂, hd₂, hy₂⟩ := hi₂.2
      obtain ⟨π₁, hπ₁, c₁, hc₁, e₁⟩ := PlaneCommuting.exists_mul_of_mem_sup hPC (hYPC hy₁)
      obtain ⟨π₂, hπ₂, c₂, hc₂, e₂⟩ := PlaneCommuting.exists_mul_of_mem_sup hPC (hYPC hy₂)
      have hn₁ : i₁ = π₁ * (c₁ * d₁⁻¹) := by
        calc i₁ = (i₁ * d₁) * d₁⁻¹ := by group
          _ = (π₁ * c₁) * d₁⁻¹ := by rw [e₁]
          _ = π₁ * (c₁ * d₁⁻¹) := by group
      have hn₂ : i₂ = π₂ * (c₂ * d₂⁻¹) := by
        calc i₂ = (i₂ * d₂) * d₂⁻¹ := by group
          _ = (π₂ * c₂) * d₂⁻¹ := by rw [e₂]
          _ = π₂ * (c₂ * d₂⁻¹) := by group
      have hc₁' : c₁ * d₁⁻¹ ∈ C := C.mul_mem hc₁ (C.inv_mem hd₁)
      have hc₂' : c₂ * d₂⁻¹ ∈ C := C.mul_mem hc₂ (C.inv_mem hd₂)
      have hn₂I : c₂ * d₂⁻¹ ∈ I := by
        have : c₂ * d₂⁻¹ = π₂⁻¹ * i₂ := by rw [hn₂]; group
        rw [this]
        exact I.mul_mem (I.inv_mem (hPI π₂ hπ₂)) (hSYI i₂ hi₂)
      have hcomm : ⁅c₁ * d₁⁻¹, c₂ * d₂⁻¹⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (hIC _ hn₂I _ hc₁').symm
      rw [hn₁, hn₂, PlaneCommuting.commutatorElement_mul_mul hIC ⟨π₁, hPI π₁ hπ₁⟩
        ⟨π₂, hPI π₂ hπ₂⟩ ⟨c₁ * d₁⁻¹, hc₁'⟩ ⟨c₂ * d₂⁻¹, hc₂'⟩]
      show ⁅π₁, π₂⁆ * ⁅c₁ * d₁⁻¹, c₂ * d₂⁻¹⁆ ∈ ⁅P, P⁆
      rw [hcomm, mul_one]
      exact Subgroup.commutator_mem_commutator hπ₁ hπ₂
  have hPY₀ : P ≤ Y₀ := hY₀ P (fun x hx => ⟨hPI x hx, hSYe x (hPSY hx)⟩) hPperf
  exact hYPC.trans (sup_le_sup_right hPY₀ C)

theorem layerInner_of_central [Finite G] {p : ℕ} (hp : p.Prime) {E I : Subgroup G} {e : G}
    (he : e ∈ E) (he1 : e ≠ 1) (hLD : LayerDataW p E I)
    (hEC : ∀ x ∈ E, ∀ d ∈ Subgroup.centralizer (I : Set G), x * d = d * x)
    (hEfaith : ∀ z ∈ E, z ∈ Subgroup.centralizer (I : Set G) → z = 1)
    (hPerf : ∀ Z : Subgroup G, Group.IsPerfect ↥Z → Z ≤ Subgroup.normalizer (I : Set G) →
      Z ≤ I ⊔ Subgroup.centralizer (I : Set G))
    (hQθ : ∀ Q : Subgroup G, Q ≤ I ⊓ Subgroup.centralizer ({e} : Set G) →
      IsComponent (Q.subgroupOf (I ⊓ Subgroup.centralizer ({e} : Set G))) → Q ≤ thetaLayer p e)
    (hΘ : ∀ Z ∈ thetaComponentsAt p e, Z ≤ Subgroup.normalizer (I : Set G))
    (hEmem : ∀ z : G, z ^ p = 1 → (∀ x ∈ E, x * z = z * x) → z ∈ E) :
    (∀ x ∈ E, ∃ l ∈ thetaLayer p e, ∃ c' ∈ Subgroup.centralizer (thetaLayer p e : Set G),
        x = l * c') ∧
      ¬ p ∣ Nat.card ↥(thetaLayer p e ⊓ Subgroup.centralizer (thetaLayer p e : Set G)) := by
  classical
  set C : Subgroup G := Subgroup.centralizer (I : Set G) with hC
  obtain ⟨ι, Q, hQH, hQc, hperfQ, hQ⟩ := hLD e he he1
  set S : Finset (Subgroup G) := (Set.toFinite (Set.range Q)).toFinset with hS
  have hSmem : ∀ Y, Y ∈ S ↔ ∃ i, Q i = Y := by
    intro Y
    simp [hS]
  have hsup : S.sup id = ⨆ i, Q i := by
    apply le_antisymm
    · exact Finset.sup_le fun Y hY => by
        obtain ⟨i, rfl⟩ := (hSmem Y).1 hY
        exact le_iSup Q i
    · exact iSup_le fun i => Finset.le_sup (f := id) ((hSmem _).2 ⟨i, rfl⟩)
  have hcommS : ∀ Y ∈ S, ∀ Y' ∈ S, Y ≠ Y' → ∀ a ∈ Y, ∀ b ∈ Y', a * b = b * a := by
    intro Y hY Y' hY' hne a ha b hb
    obtain ⟨i, rfl⟩ := (hSmem Y).1 hY
    obtain ⟨j, rfl⟩ := (hSmem Y').1 hY'
    rcases eq_or_commutator_eq_bot_of_components (hQH i) (hQH j) (hQc i) (hQc j) with hij | hij
    · exact absurd hij hne
    · have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hij ha
      exact (Subgroup.mem_centralizer_iff.1 this b hb).symm
  have hinS : ∀ Y ∈ S, ∀ x ∈ E, ∃ y ∈ Y, ∃ c ∈ Subgroup.centralizer (Y : Set G), x = y * c := by
    intro Y hY x hx
    obtain ⟨i, rfl⟩ := (hSmem Y).1 hY
    exact (hQ i).1 x hx
  have hzS : ∀ Y ∈ S, ∀ z ∈ Y ⊓ Subgroup.centralizer (Y : Set G), ¬ p ∣ orderOf z := by
    intro Y hY z hz hdvd
    obtain ⟨i, rfl⟩ := (hSmem Y).1 hY
    exact (hQ i).2 (hdvd.trans (Subgroup.orderOf_dvd_natCard _ hz))
  have hA := inner_finset_sup S hcommS hinS
  have hB := noP_finset_sup hp S hcommS hzS
  set Y₀ : Subgroup G := S.sup id with hY₀
  have hY₀I : Y₀ ≤ I := by
    rw [hsup]
    exact iSup_le fun i => (hQH i).trans inf_le_left
  have hQL : ∀ i, Q i ≤ thetaLayer p e := fun i => hQθ (Q i) (hQH i) (hQc i)
  have hY₀L : Y₀ ≤ thetaLayer p e := by
    rw [hsup]
    exact iSup_le hQL
  have hIC : ∀ a ∈ I, ∀ b ∈ C, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 hb a ha
  have hCe : ∀ d ∈ C, e * d = d * e := fun d hd => hEC e he d hd
  have hperfY₀ : ∀ P : Subgroup G, P ≤ I ⊓ Subgroup.centralizer ({e} : Set G) →
      Group.IsPerfect ↥P → P ≤ Y₀ := by
    intro P hPH hPperf
    rw [hsup]
    exact hperfQ P hPH hPperf
  have hLeW : thetaLayer p e ≤ Y₀ ⊔ C := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨Y, hY, hxY⟩
    have hperf := isPerfect_of_mem_thetaComponentsAt hY
    have hYIC : Y ≤ I ⊔ C := hPerf Y hperf (hΘ Y hY)
    have hYCe : Y ≤ Subgroup.centralizer ({e} : Set G) := (mem_thetaComponentsAt_iff.1 hY).1
    exact perfect_le_sup_of_commute hIC hCe hperfY₀ hperf hYIC hYCe hxY
  have hinn : ∀ x ∈ E, ∃ l ∈ thetaLayer p e, ∃ c' ∈ Subgroup.centralizer (thetaLayer p e : Set G),
      x = l * c' := by
    intro x hx
    obtain ⟨q, hq, c₀, hc₀, hxqc⟩ := hA x hx
    refine ⟨q, hY₀L hq, c₀, ?_, hxqc⟩
    have hc₀C : ∀ w ∈ C, c₀ * w = w * c₀ := by
      intro w hw
      have h1 : Commute q w := hIC q (hY₀I hq) w hw
      have h2 : Commute x w := hEC x hx w hw
      have hc₀eq : c₀ = q⁻¹ * x := by rw [hxqc]; group
      rw [hc₀eq]
      exact (h1.inv_left.mul_left h2).eq
    have hle : Y₀ ⊔ C ≤ Subgroup.centralizer ({c₀} : Set G) := by
      refine sup_le (fun w hw => ?_) (fun w hw => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.1 hc₀ w hw)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hc₀C w hw).symm
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle (hLeW hw))
  refine ⟨hinn, ?_⟩
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hzo⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(thetaLayer p e ⊓ Subgroup.centralizer (thetaLayer p e : Set G))) p hdvd
  have hzL : (z : G) ∈ thetaLayer p e := z.2.1
  have hzC : (z : G) ∈ Subgroup.centralizer (thetaLayer p e : Set G) := z.2.2
  have hzo' : orderOf (z : G) = p := by rw [Subgroup.orderOf_coe]; exact hzo
  have hY₀C : ∀ a ∈ Y₀, ∀ b ∈ C, a * b = b * a := fun a ha b hb => hIC a (hY₀I ha) b hb
  obtain ⟨y, hy, d, hd, hzyd⟩ := PlaneCommuting.exists_mul_of_mem_sup hY₀C (hLeW hzL)
  have hyZ : y ∈ Y₀ ⊓ Subgroup.centralizer (Y₀ : Set G) := by
    refine ⟨hy, ?_⟩
    show y ∈ Subgroup.centralizer (Y₀ : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 : w * (z : G) = (z : G) * w := Subgroup.mem_centralizer_iff.1 hzC w (hY₀L hw)
    have h2 : w * d = d * w := hIC w (hY₀I hw) d hd
    have hy' : y = (z : G) * d⁻¹ := by rw [hzyd]; group
    rw [hy']
    have hc2 : Commute w d⁻¹ := (show Commute w d from h2).inv_right
    exact ((show Commute w (z : G) from h1).mul_right hc2).eq
  have hyp : ¬ p ∣ orderOf y := hB y hyZ
  have hyd : Commute y d := hIC y (hY₀I hy) d hd
  set m := orderOf y with hm
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hyp
  have hzm : (z : G) ^ m = d ^ m := by
    rw [hzyd, hyd.mul_pow, hm, pow_orderOf_eq_one, one_mul]
  have hzmo : orderOf ((z : G) ^ m) = p := by
    rw [Nat.Coprime.orderOf_pow (by rw [hzo']; exact hcop), hzo']
  have hz'C : (z : G) ^ m ∈ C := by rw [hzm]; exact C.pow_mem hd m
  have hz'comm : ∀ x ∈ E, x * (z : G) ^ m = (z : G) ^ m * x := by
    intro x hx
    obtain ⟨l, hl, c', hc', hxlc⟩ := hinn x hx
    have hzl : Commute (z : G) l := (Subgroup.mem_centralizer_iff.1 hzC l hl).symm
    have hzc' : Commute (z : G) c' := (Subgroup.mem_centralizer_iff.1 hc' (z : G) hzL)
    have : Commute (z : G) x := by
      rw [hxlc]
      exact hzl.mul_right hzc'
    exact (this.pow_left m).symm.eq
  have hz'p : ((z : G) ^ m) ^ p = 1 := by
    have := pow_orderOf_eq_one ((z : G) ^ m)
    rwa [hzmo] at this
  have hz'E : (z : G) ^ m ∈ E := hEmem _ hz'p hz'comm
  have h1 : (z : G) ^ m = 1 := hEfaith _ hz'E hz'C
  have h2 : orderOf ((z : G) ^ m) = 1 := by rw [h1, orderOf_one]
  rw [h2] at hzmo
  exact hp.one_lt.ne hzmo

@[expose] def KFPerfNormalizerFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∀ Z : Subgroup G, Group.IsPerfect ↥Z → Z ≤ lieNormalizer p E →
      Z ≤ lieGenerated p E ⊔ Subgroup.centralizer (lieGenerated p E : Set G)

@[expose] def KFCompLayerFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∀ e ∈ E, e ≠ 1 → ∀ Q : Subgroup G,
      Q ≤ lieGenerated p E ⊓ Subgroup.centralizer ({e} : Set G) →
      IsComponent (Q.subgroupOf (lieGenerated p E ⊓ Subgroup.centralizer ({e} : Set G))) →
      Q ≤ thetaLayer p e

@[expose] def KFInnLayerFiveP5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∀ e ∈ E, e ≠ 1 → CentralizesE p E e → (∀ Z ∈ thetaComponentsAt p e, Z ≤ lieNormalizer p E) →
    p = 5 → ¬ E ≤ lieGenerated p E → ∀ x ∈ E, ∃ l ∈ E ⊓ thetaLayer p e,
      ∃ c' ∈ E ⊓ Subgroup.centralizer (thetaLayer p e : Set G), x = l * c'

section Five

variable [Finite G]

theorem not_dvd_inf_centralizer_five (hEin : U5K.U5EInndiag) {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) :
    ¬ p ∣ Nat.card ↥(lieGenerated p E ⊓ Subgroup.centralizer (lieGenerated p E : Set G)) := by
  set I := lieGenerated p E with hI
  obtain ⟨f, hf, hpf, ⟨e⟩, -⟩ := id hout
  have hp := h15.h12.prime
  have hEI : E ≤ Subgroup.normalizer (I : Set G) := E_le_normalizer_lieGenerated hp
  have hker := U5K.ker_not_dvd_p_of_max hp e h15.h12.E_elem hEI h15.h12.A_le_E h15.h12.E_le
    h15.h12.E_max (fun x hx hxE h => (hEin G p A c L E h15 hF hout f hf e x hx hxE).2 h)
  intro hdvd
  apply hker
  have hle : I ⊓ Subgroup.centralizer (I : Set G) ≤ U5K.kerG I e := by
    intro z hz
    refine U5K.mem_kerG.2 ⟨I.le_normalizer hz.1, ?_⟩
    have h4 : (⟨z, hz.1⟩ : ↥I) ∈ Subgroup.center ↥I := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hz.2 g g.2)
    have h3 := U5K.U5Act_of_mem I e ⟨z, hz.1⟩
    have h5 : (↑(⟨z, hz.1⟩ : ↥I) : ↥I ⧸ Subgroup.center ↥I) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr h4
    rw [h5, map_one] at h3
    exact h3.trans (map_one _)
  have h6 := Subgroup.card_dvd_of_le hle
  rw [U5K.card_kerG] at h6
  exact hdvd.trans h6

theorem eq_one_of_mem_centralizer_five (hEin : U5K.U5EInndiag) {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) {z : G} (hzE : z ∈ E)
    (hzC : z ∈ Subgroup.centralizer (lieGenerated p E : Set G)) : z = 1 := by
  set I := lieGenerated p E with hI
  obtain ⟨f, hf, hpf, ⟨e⟩, -⟩ := id hout
  have hzN : z ∈ Subgroup.normalizer (I : Set G) := (Subgroup.centralizer_le_normalizer _) hzC
  refine (hEin G p A c L E h15 hF hout f hf e z hzN hzE).2 ?_
  refine MulEquiv.ext fun w => ?_
  obtain ⟨y, rfl⟩ := e.surjective w
  obtain ⟨i, rfl⟩ := QuotientGroup.mk_surjective y
  rw [U5K.U5Act_apply]
  have h1 : I.normalizerMonoidHom ⟨z, hzN⟩ i = i := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have := Subgroup.mem_centralizer_iff.1 hzC i i.2
    show z * (i : G) * z⁻¹ = (i : G)
    rw [← this]
    group
  rw [h1]
  rfl

theorem kfInnLayerFive_at (hEin : U5K.U5EInndiag) (hPerf : KFPerfNormalizerFive)
    (hComp : KFCompLayerFive) {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E))
    (hEC : ∀ x ∈ E, ∀ d ∈ Subgroup.centralizer (lieGenerated p E : Set G), x * d = d * x)
    {e : G} (he : e ∈ E) (he1 : e ≠ 1)
    (hΘ : ∀ Z ∈ thetaComponentsAt p e, Z ≤ lieNormalizer p E) :
    ∀ x ∈ E, ∃ l ∈ E ⊓ thetaLayer p e,
      ∃ c' ∈ E ⊓ Subgroup.centralizer (thetaLayer p e : Set G), x = l * c' := by
  classical
  have h := h15.h12
  have hp := h.prime
  have hRow : LayerDataW p E (lieGenerated p E) := layerRowFive_of hEin G p A c L E h15 hF hout
  have hEel : IsElementaryAbelian p ↥E := h.E_elem
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEel.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEpow : ∀ x ∈ E, x ^ p = 1 := fun x hx =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) x hx
  have hEmem : ∀ z : G, z ^ p = 1 → (∀ x ∈ E, x * z = z * x) → z ∈ E := by
    intro z hzp hz
    have hzel : IsElementaryAbelian p ↥(Subgroup.zpowers z) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one hzp
    have hcentz : Subgroup.zpowers z ≤ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro y hy
      exact hz y hy
    have hsup := IsElementaryAbelian.sup_of_le_centralizer (p := p) hcentz
    have hF' : E ⊔ Subgroup.zpowers z = E := h.E_max_global _ hsup le_sup_left
    rw [← hF']
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  obtain ⟨hinn, hcenter⟩ := layerInner_of_central hp he he1 hRow hEC
    (fun z hzE hzC => eq_one_of_mem_centralizer_five hEin h15 hF hout hzE hzC)
    (hPerf G p A c L E h15 hF hout) (hComp G p A c L E h15 hF hout e he he1) hΘ hEmem
  refine inf_mul_inf_of_inner hp hEcomm hEpow ?_ hinn hcenter
  intro F hFc hFp hFE hEF
  have hFel : IsElementaryAbelian p ↥F :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hFc a a.2 b b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (by simpa using hFp a a.2) }
  exact (h.E_max_global F hFel hEF).le

theorem kfInnLayerFive_of_facts (hMod : KFU5Mod) (hAt : KFU5At) (h5 : U5FiveInndiag)
    (hPerf : KFPerfNormalizerFive) (hComp : KFCompLayerFive) (hP5 : KFInnLayerFiveP5) :
    KFInnLayerFive := by
  intro G _ _ p A c L E h15 hF hout e he he1 hcen hΘ
  classical
  by_cases hEI : E ≤ lieGenerated p E
  · exact kfInnLayerFive_at (U5K.u5EInndiag_of hMod hAt h5) hPerf hComp h15 hF hout
      (fun x hx d hd => Subgroup.mem_centralizer_iff.1 hd x (hEI hx)) he he1 hΘ
  · have hp5 : p = 5 := by
      by_contra hne
      exact hEI (Sec153.E_le_of_ne_five hMod hAt G p A c L E h15 hF hout hne)
    exact hP5 G p A c L E h15 hF hout e he he1 hcen hΘ hp5 hEI

end Five

end CFSG.RankThree.PartOne.K159

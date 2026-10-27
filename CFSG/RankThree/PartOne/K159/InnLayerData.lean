module

public import CFSG.RankThree.PartOne.K159.InnLayer
public import CFSG.RankThree.PartOne.K159.InnLayerComb
public import CFSG.RankThree.PartOne.S15K.LayerData
import CFSG.RankThree.PartOne.S10.PlaneTwoGroupLemmas

public section

namespace CFSG.RankThree.PartOne.K159

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S15K
open scoped commutatorElement

@[expose] def KFInnLayerData : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) → E = A →
    LayerData p E (lieGenerated p E) ∧ E ≤ lieGenerated p E ∧
    ¬ p ∣ Nat.card ↥(lieGenerated p E ⊓ Subgroup.centralizer (lieGenerated p E : Set G)) ∧
    (∀ Z : Subgroup G, Group.IsPerfect ↥Z → Z ≤ lieNormalizer p E →
      Z ≤ lieGenerated p E ⊔ Subgroup.centralizer (lieGenerated p E : Set G)) ∧
    (∀ e ∈ E, e ≠ 1 → ∀ Q : Subgroup G,
      Q ≤ lieGenerated p E ⊓ Subgroup.centralizer ({e} : Set G) →
      IsComponent (Q.subgroupOf (lieGenerated p E ⊓ Subgroup.centralizer ({e} : Set G))) →
      Q ≤ thetaLayer p e)

variable {G : Type} [Group G]

theorem mem_E_of_commute [Finite G] {p : ℕ} {A c : _} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hEA : E = A) {z : G} (hzp : z ^ p = 1)
    (hz : ∀ x ∈ E, x * z = z * x) : z ∈ E := by
  classical
  have hEel : IsElementaryAbelian p ↥E := h.E_elem
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEel.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEpow : ∀ x ∈ E, x ^ p = 1 := fun x hx =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) x hx
  set S : Set G := (E : Set G) ∪ {z} with hS
  have hScomm : ∀ s ∈ S, ∀ t ∈ S, Commute s t := by
    rintro s (hs | hs) t (ht | ht)
    · exact hEcomm s hs t ht
    · rw [Set.mem_singleton_iff] at ht
      rw [ht]
      exact hz s hs
    · rw [Set.mem_singleton_iff] at hs
      rw [hs]
      exact (hz t ht).symm
    · rw [Set.mem_singleton_iff] at hs ht
      rw [hs, ht]
  have hSpow : ∀ s ∈ S, s ^ p = 1 := by
    rintro s (hs | hs)
    · exact hEpow s hs
    · rw [Set.mem_singleton_iff] at hs
      rw [hs]
      exact hzp
  set F : Subgroup G := Subgroup.closure S with hF
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    (commute_of_mem_closure' hScomm hx hy).eq
  have hFpow : ∀ x ∈ F, x ^ p = 1 := fun x hx => pow_eq_one_of_mem_closure' hScomm hSpow hx
  have hEF : E ≤ F := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hFA : F ≤ Subgroup.centralizer (A : Set G) := by
    have hle : F ≤ Subgroup.centralizer (E : Set G) := by
      refine (Subgroup.closure_le _).2 fun s hs => ?_
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro y hy
      rcases hs with hs | hs
      · exact hEcomm y hy s hs
      · rw [Set.mem_singleton_iff] at hs
        rw [hs]
        exact hz y hy
    rw [← hEA]
    exact hle
  have hFel : IsElementaryAbelian p ↥F :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hFcomm a a.2 b b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (by simpa using hFpow a a.2) }
  have hFE : F = E := h.E_max F hFel hFA hEF
  have hzF : z ∈ F := Subgroup.subset_closure (Or.inr rfl)
  rw [hFE] at hzF
  exact hzF

theorem kfInnLayerInner_of_data (hdata : KFInnLayerData) : KFInnLayerInner := by
  classical
  intro G _ _ p A c L E h15 hF hout hEA e he he1 hΘ
  obtain ⟨hLD, hEI, hZI, hPerf, hQθ⟩ := hdata G p A c L E h15 hF hout hEA
  have h := h15.h12
  have hp : p.Prime := h.prime
  set I : Subgroup G := lieGenerated p E with hI
  set C : Subgroup G := Subgroup.centralizer (I : Set G) with hC
  set H : Subgroup G := I ⊓ Subgroup.centralizer ({e} : Set G) with hH
  obtain ⟨ι, Q, hQH, hQc, hder, hQ⟩ := hLD e he he1
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
  have hQL : ∀ i, Q i ≤ thetaLayer p e := fun i => hQθ e he he1 (Q i) (hQH i) (hQc i)
  have hY₀L : Y₀ ≤ thetaLayer p e := by
    rw [hsup]
    exact iSup_le hQL
  have hIC : ∀ a ∈ I, ∀ b ∈ C, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 hb a ha
  have hCe : ∀ d ∈ C, e * d = d * e := fun d hd => Subgroup.mem_centralizer_iff.1 hd e (hEI he)
  have hLeW : thetaLayer p e ≤ Y₀ ⊔ C := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨Y, hY, hxY⟩
    have hperf := isPerfect_of_mem_thetaComponentsAt hY
    have hYIC : Y ≤ I ⊔ C := hPerf Y hperf (hΘ Y hY)
    have hYCe : Y ≤ Subgroup.centralizer ({e} : Set G) := (mem_thetaComponentsAt_iff.1 hY).1
    have hYW : Y ≤ Y₀ ⊔ C := by
      calc Y = ⁅Y, Y⁆ := ((Subgroup.isPerfect_iff).1 hperf).symm
        _ ≤ Y₀ ⊔ C := by
          rw [Subgroup.commutator_def]
          refine (Subgroup.closure_le _).2 ?_
          rintro _ ⟨y₁, hy₁, y₂, hy₂, rfl⟩
          obtain ⟨i₁, hi₁, d₁, hd₁, h₁⟩ := PlaneCommuting.exists_mul_of_mem_sup hIC (hYIC hy₁)
          obtain ⟨i₂, hi₂, d₂, hd₂, h₂⟩ := PlaneCommuting.exists_mul_of_mem_sup hIC (hYIC hy₂)
          have hinH : ∀ y ∈ Y, ∀ i ∈ I, ∀ d ∈ C, y = i * d → i ∈ H := by
            intro y hy i hi d hd hyid
            refine ⟨hi, ?_⟩
            show i ∈ Subgroup.centralizer ({e} : Set G)
            rw [Subgroup.mem_centralizer_singleton_iff]
            have hey : Commute e y :=
              (show Commute y e from Subgroup.mem_centralizer_singleton_iff.1 (hYCe hy)).symm
            have hed : Commute e d := hCe d hd
            have hi' : i = y * d⁻¹ := by rw [hyid]; group
            have : Commute e i := by
              rw [hi']
              exact hey.mul_right hed.inv_right
            exact this.eq.symm
          have hi₁H : i₁ ∈ H := hinH y₁ hy₁ i₁ hi₁ d₁ hd₁ h₁
          have hi₂H : i₂ ∈ H := hinH y₂ hy₂ i₂ hi₂ d₂ hd₂ h₂
          rw [h₁, h₂, PlaneCommuting.commutatorElement_mul_mul hIC ⟨i₁, hi₁⟩ ⟨i₂, hi₂⟩
            ⟨d₁, hd₁⟩ ⟨d₂, hd₂⟩]
          refine Subgroup.mul_mem_sup ?_ ?_
          · have := Subgroup.commutator_mem_commutator hi₁H hi₂H
            rw [hder, ← hsup] at this
            exact this
          · rw [commutatorElement_def]
            exact C.mul_mem (C.mul_mem (C.mul_mem hd₁ hd₂) (C.inv_mem hd₁)) (C.inv_mem hd₂)
    exact hYW hxY
  have hinn : ∀ x ∈ E, ∃ l ∈ thetaLayer p e, ∃ c' ∈ Subgroup.centralizer (thetaLayer p e : Set G),
      x = l * c' := by
    intro x hx
    obtain ⟨q, hq, c₀, hc₀, hxqc⟩ := hA x hx
    refine ⟨q, hY₀L hq, c₀, ?_, hxqc⟩
    have hc₀I : c₀ ∈ I := by
      have : c₀ = q⁻¹ * x := by rw [hxqc]; group
      rw [this]
      exact I.mul_mem (I.inv_mem (hY₀I hq)) (hEI hx)
    have hle : Y₀ ⊔ C ≤ Subgroup.centralizer ({c₀} : Set G) := by
      refine sup_le (fun w hw => ?_) (fun w hw => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.1 hc₀ w hw)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hIC c₀ hc₀I w hw).symm
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
  have hz'E : (z : G) ^ m ∈ E := mem_E_of_commute h hEA hz'p hz'comm
  have hz'I : (z : G) ^ m ∈ I ⊓ Subgroup.centralizer (I : Set G) := ⟨hEI hz'E, hz'C⟩
  have hdvd' : orderOf ((z : G) ^ m) ∣ Nat.card ↥(I ⊓ Subgroup.centralizer (I : Set G)) :=
    Subgroup.orderOf_dvd_natCard _ hz'I
  rw [hzmo] at hdvd'
  exact hZI hdvd'

theorem kfInnLayer_of_data (hdata : KFInnLayerData) : KFInnLayer :=
  kfInnLayer_of_inner (kfInnLayerInner_of_data hdata)

end CFSG.RankThree.PartOne.K159

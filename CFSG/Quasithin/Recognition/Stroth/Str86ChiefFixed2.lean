module

public import CFSG.Quasithin.Recognition.Stroth.Str86ChiefFixed

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem exists_first_meet {H U Lo Hi Y : Subgroup G} {n : ℕ}
    (hser : F112W.IsChiefSeriesBetween H U Lo Hi n)
    (hYHi : Y ≤ Hi) (hY : ¬ Y ≤ Lo) :
    ∃ L K : Subgroup G,
      Lo ≤ L ∧ L < K ∧ K ≤ Hi ∧ IsChiefStep H U L K ∧
      ¬ Y ≤ L ∧ Y ⊓ L ≤ Lo ∧ ¬ Y ⊓ K ≤ Lo := by
  induction hser generalizing Y with
  | refl => exact absurd hYHi hY
  | @central Hi' L n hstep hc hs ih =>
    by_cases hYL : Y ⊓ L ≤ Lo
    · refine ⟨L, Hi', hs.le, hstep.2.2.1, le_rfl, hstep, ?_, hYL, ?_⟩
      · intro hYle
        have : Y ≤ Lo := by simpa [inf_eq_left.mpr hYle] using hYL
        exact hY this
      · simpa [inf_eq_left.mpr hYHi] using hY
    · obtain ⟨L', K', hLoL', hL'K', hK'L, hstep', hYL', hYL'Lo, hYK'Lo⟩ :=
        ih inf_le_right hYL
      have hL'L : L' ≤ L := hL'K'.le.trans hK'L
      refine ⟨L', K', hLoL', hL'K', hK'L.trans hstep.2.2.1.le, hstep', ?_, ?_, ?_⟩
      · intro hYle
        exact hYL' (inf_le_left.trans hYle)
      · have h : (Y ⊓ L) ⊓ L' ≤ Lo := hYL'Lo
        rwa [inf_assoc, inf_eq_right.mpr hL'L] at h
      · intro h
        apply hYK'Lo
        rwa [inf_assoc, inf_eq_right.mpr hK'L]
  | @noncentral Hi' L n hstep hnc hs ih =>
    by_cases hYL : Y ⊓ L ≤ Lo
    · refine ⟨L, Hi', hs.le, hstep.2.2.1, le_rfl, hstep, ?_, hYL, ?_⟩
      · intro hYle
        have : Y ≤ Lo := by simpa [inf_eq_left.mpr hYle] using hYL
        exact hY this
      · simpa [inf_eq_left.mpr hYHi] using hY
    · obtain ⟨L', K', hLoL', hL'K', hK'L, hstep', hYL', hYL'Lo, hYK'Lo⟩ :=
        ih inf_le_right hYL
      have hL'L : L' ≤ L := hL'K'.le.trans hK'L
      refine ⟨L', K', hLoL', hL'K', hK'L.trans hstep.2.2.1.le, hstep', ?_, ?_, ?_⟩
      · intro hYle
        exact hYL' (inf_le_left.trans hYle)
      · have h : (Y ⊓ L) ⊓ L' ≤ Lo := hYL'Lo
        rwa [inf_assoc, inf_eq_right.mpr hL'L] at h
      · intro h
        apply hYK'Lo
        rwa [inf_assoc, inf_eq_right.mpr hK'L]

theorem relIndex_le_pow_of_fixedPointFree
    {H S U Lo Hi Y : Subgroup G} {r n : ℕ} {d : G}
    (hU : IsElemAbelian 2 U) (hUH : U ≤ H)
    (hHU : H ≤ Subgroup.normalizer (U : Set G))
    (hSH : S ≤ H) (hser : F112W.IsChiefSeriesBetween H U Lo Hi n)
    (hnat : ∀ Lo' Hi' : Subgroup G, Lo ≤ Lo' → Hi' ≤ Hi → IsChiefStep H U Lo' Hi' →
      ¬ IsCentralStep H Lo' Hi' → ∀ X : Subgroup G, Lo' ≤ X → X ≤ Hi' →
        (∀ s ∈ S, ∀ x ∈ X, s * x * s⁻¹ * x⁻¹ ∈ Lo') → Lo'.relIndex X ≤ r)
    (hLoY : Lo ≤ Y) (hYHi : Y ≤ Hi)
    (hYS : ∀ s ∈ S, ∀ y ∈ Y, s * y * s⁻¹ * y⁻¹ ∈ Lo)
    (hdH : d ∈ H) (hdo : Odd (orderOf d)) (hdY : ∀ y ∈ Y, d * y * d⁻¹ ∈ Y)
    (hfpf : ∀ y ∈ Y, d * y * d⁻¹ * y⁻¹ ∈ Lo → y ∈ Lo) :
    Lo.relIndex Y ≤ r ^ n := by
  induction hser generalizing Y with
  | refl =>
    have hYLo : Y = Lo := le_antisymm (hYHi.trans (le_of_eq rfl)) hLoY
    rw [hYLo, Subgroup.relIndex_self, pow_zero]
  | @central Hi' L n hstep hc hs ih =>
    have hLoL : Lo ≤ L := hs.le
    have hYH : Y ≤ H := (hYHi.trans hstep.1.1).trans hUH
    have hY2 : ∀ y ∈ Y, y * y = 1 := fun y hy =>
      by simpa [pow_two] using hU.2 y ((hYHi.trans hstep.1.1) hy)
    have hYab : ∀ y ∈ Y, ∀ z ∈ Y, y * z = z * y := fun y hy z hz =>
      congrArg Subtype.val
        (hU.1.is_comm.comm ⟨y, (hYHi.trans hstep.1.1) hy⟩
          ⟨z, (hYHi.trans hstep.1.1) hz⟩)
    have hdL : ∀ y ∈ L, d * y * d⁻¹ ∈ L := by
      intro y hy
      exact (Subgroup.mem_normalizer_iff.mp
        ((D14.le_normalizer_of_isNormalIn (H := H) (U := U) hstep.2.1) hdH) y).mp hy
    have hYL : Y ≤ L := by
      intro y hy
      exact mem_of_comm_mem_of_fixedPointFree hY2 hYab hLoL hy hdY hdL hdo
        (fun z hz => hfpf z hz) (hc d hdH y (hYHi hy))
    have hY' : Y ⊓ L = Y := inf_eq_left.mpr hYL
    have hLoY' : Lo ≤ Y ⊓ L := le_inf hLoY hLoL
    have hY'Hi : Y ⊓ L ≤ L := inf_le_right
    have hY'S : ∀ s ∈ S, ∀ y ∈ Y ⊓ L, s * y * s⁻¹ * y⁻¹ ∈ Lo :=
      fun s hs y hy => hYS s hs y hy.1
    have hdY' : ∀ y ∈ Y ⊓ L, d * y * d⁻¹ ∈ Y ⊓ L :=
      fun y hy => ⟨hdY y hy.1, hdL y hy.2⟩
    have hfpf' : ∀ y ∈ Y ⊓ L, d * y * d⁻¹ * y⁻¹ ∈ Lo → y ∈ Lo :=
      fun y hy => hfpf y hy.1
    have hnatL : ∀ Lo' Hi' : Subgroup G, Lo ≤ Lo' → Hi' ≤ L → IsChiefStep H U Lo' Hi' →
        ¬ IsCentralStep H Lo' Hi' → ∀ X : Subgroup G, Lo' ≤ X → X ≤ Hi' →
          (∀ s ∈ S, ∀ x ∈ X, s * x * s⁻¹ * x⁻¹ ∈ Lo') → Lo'.relIndex X ≤ r :=
      fun Lo' Hi' h1 h2 h3 h4 => hnat Lo' Hi' h1 (h2.trans hstep.2.2.1.le) h3 h4
    have := ih hnatL (Y := Y ⊓ L) hLoY' hY'Hi hY'S hdY' hfpf'
    simpa [hY'] using this
  | @noncentral Hi' L n hstep hnc hs ih =>
    have hLoL : Lo ≤ L := hs.le
    have hYH : Y ≤ H := (hYHi.trans hstep.1.1).trans hUH
    have hLoY' : Lo ≤ Y ⊓ L := le_inf hLoY hLoL
    have hY'Hi : Y ⊓ L ≤ L := inf_le_right
    have hY'S : ∀ s ∈ S, ∀ y ∈ Y ⊓ L, s * y * s⁻¹ * y⁻¹ ∈ Lo :=
      fun s hs y hy => hYS s hs y hy.1
    have hdL : ∀ y ∈ L, d * y * d⁻¹ ∈ L := by
      intro y hy
      exact (Subgroup.mem_normalizer_iff.mp
        ((D14.le_normalizer_of_isNormalIn (H := H) (U := U) hstep.2.1) hdH) y).mp hy
    have hdY' : ∀ y ∈ Y ⊓ L, d * y * d⁻¹ ∈ Y ⊓ L := fun y hy =>
      ⟨hdY y hy.1, hdL y hy.2⟩
    have hfpf' : ∀ y ∈ Y ⊓ L, d * y * d⁻¹ * y⁻¹ ∈ Lo → y ∈ Lo :=
      fun y hy => hfpf y hy.1
    have hnatL : ∀ Lo' Hi' : Subgroup G, Lo ≤ Lo' → Hi' ≤ L → IsChiefStep H U Lo' Hi' →
        ¬ IsCentralStep H Lo' Hi' → ∀ X : Subgroup G, Lo' ≤ X → X ≤ Hi' →
          (∀ s ∈ S, ∀ x ∈ X, s * x * s⁻¹ * x⁻¹ ∈ Lo') → Lo'.relIndex X ≤ r :=
      fun Lo' Hi' h1 h2 h3 h4 => hnat Lo' Hi' h1 (h2.trans hstep.2.2.1.le) h3 h4
    have ih' := ih hnatL (Y := Y ⊓ L) hLoY' hY'Hi hY'S hdY' hfpf'
    have hYLnorm : Y ≤ Subgroup.normalizer (L : Set G) :=
      hYH.trans (D14.le_normalizer_of_isNormalIn (H := H) (U := U) hstep.2.1)
    have hcommSup : ∀ s ∈ S, ∀ x ∈ Y ⊔ L, s * x * s⁻¹ * x⁻¹ ∈ L := by
      intro s hs x hx
      have hYnormL : Y ≤ Subgroup.normalizer (L : Set G) := hYLnorm
      have hVS : ⁅L, S⁆ ≤ L :=
        F112W.commutator_le_self_of_le_normalizer
          (hSH.trans (D14.le_normalizer_of_isNormalIn (H := H) (U := U) hstep.2.1))
      have hYSup : ⁅Y, S⁆ ≤ L := by
        rw [Subgroup.commutator_le]
        intro y hy s' hs'
        have h : s' * y * s'⁻¹ * y⁻¹ ∈ Lo := hYS s' hs' y hy
        have e : ⁅y, s'⁆ = (s' * y * s'⁻¹ * y⁻¹)⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact hLoL (Lo.inv_mem h)
      have hsup : ⁅Y ⊔ L, S⁆ ≤ L :=
        D14.commutator_sup_le_of (W := Y) (V := L) (Q := S) (M := L)
          hYnormL hYnormL hVS hYSup
      have hsup' : ⁅S, Y ⊔ L⁆ ≤ L := by
        rw [Subgroup.commutator_comm]
        exact hsup
      have hmem : ⁅s, x⁆ ∈ ⁅S, Y ⊔ L⁆ := Subgroup.commutator_mem_commutator hs hx
      simpa [commutatorElement_def] using hsup' hmem
    have hnat' := hnat L Hi' hLoL le_rfl hstep hnc (Y ⊔ L) le_sup_right
      (sup_le hYHi hstep.2.2.1.le) hcommSup
    have hrel : (Y ⊓ L).relIndex Y = L.relIndex (Y ⊔ L) := by
      rw [inf_comm, Subgroup.inf_relIndex_right]
      exact (B6.relIndex_sup_eq_of_le_normalizer hYLnorm).symm
    have hmul : Lo.relIndex (Y ⊓ L) * (Y ⊓ L).relIndex Y = Lo.relIndex Y :=
      Subgroup.relIndex_mul_relIndex (H := Lo) (K := Y ⊓ L) (L := Y) hLoY' inf_le_left
    rw [← hmul]
    calc Lo.relIndex (Y ⊓ L) * (Y ⊓ L).relIndex Y
        ≤ r ^ n * r := Nat.mul_le_mul ih' (hrel.trans_le hnat')
      _ = r ^ (n + 1) := by rw [pow_succ]

theorem _root_.CFSG.Quasithin.F112W.IsChiefSeriesBetween.le_right_of_ne_bot
    {H U W N : Subgroup G} {n : ℕ}
    (h : F112W.IsChiefSeriesBetween H U W N n) (hWN : W < N) : N ≤ U := by
  induction h with
  | refl => exact absurd rfl hWN.ne
  | central hstep _ _ _ => exact hstep.1.1
  | noncentral hstep _ _ _ => exact hstep.1.1

theorem exists_not_fixed_of_fixedPointFree
    {H S U Lo Hi Y : Subgroup G} {n : ℕ} {d d' : G}
    (hU : IsElemAbelian 2 U) (hUH : U ≤ H)
    (hHU : H ≤ Subgroup.normalizer (U : Set G))
    (hSH : S ≤ H) (hser : F112W.IsChiefSeriesBetween H U Lo Hi n)
    (htor : ∀ Lo' Hi' : Subgroup G, Lo ≤ Lo' → Hi' ≤ Hi → IsChiefStep H U Lo' Hi' →
      ¬ IsCentralStep H Lo' Hi' → ∀ x ∈ Hi',
        (∀ s ∈ S, s * x * s⁻¹ * x⁻¹ ∈ Lo') →
          d' * x * d'⁻¹ * x⁻¹ ∈ Lo' → x ∈ Lo')
    (hLoY : Lo ≤ Y) (hYHi : Y ≤ Hi) (hY1 : Lo < Y)
    (hYS : ∀ s ∈ S, ∀ y ∈ Y, s * y * s⁻¹ * y⁻¹ ∈ Lo)
    (hdH : d ∈ H) (hdo : Odd (orderOf d)) (hdY : ∀ y ∈ Y, d * y * d⁻¹ ∈ Y)
    (hfpf : ∀ y ∈ Y, d * y * d⁻¹ * y⁻¹ ∈ Lo → y ∈ Lo)
    (hd'Y : ∀ y ∈ Y, d' * y * d'⁻¹ ∈ Y) :
    ∃ y ∈ Y, d' * y * d'⁻¹ * y⁻¹ ∉ Lo := by
  have hLoHi : Lo < Hi := lt_of_lt_of_le hY1 hYHi
  have hHiU : Hi ≤ U := hser.le_right_of_ne_bot hLoHi
  obtain ⟨L, K, hLoL, hLK, hKHi, hstep, hYLnot, hYLlo, hYKnotLo⟩ :=
    exists_first_meet hser hYHi (fun h => hY1.2 h)
  have hnotSub : ¬ Y ⊓ K ≤ L := by
    intro h
    have hle : Y ⊓ K ≤ Y ⊓ L := le_inf inf_le_left h
    have heq : Y ⊓ K = Y ⊓ L := le_antisymm hle (inf_le_inf_left Y hLK.le)
    exact hYKnotLo (heq.trans_le hYLlo)
  obtain ⟨x, hxYK, hxL⟩ := Set.not_subset.mp hnotSub
  have hxY : x ∈ Y := hxYK.1
  have hxK : x ∈ K := hxYK.2
  have hxLo : x ∉ Lo := fun h => hxL (hLoL h)
  have hYH : Y ≤ H := (hYHi.trans hHiU).trans hUH
  have hY2 : ∀ y ∈ Y, y * y = 1 := fun y hy =>
    by simpa [pow_two] using hU.2 y ((hYHi.trans hHiU) hy)
  have hYab : ∀ y ∈ Y, ∀ z ∈ Y, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val
      (hU.1.is_comm.comm ⟨y, (hYHi.trans hHiU) hy⟩ ⟨z, (hYHi.trans hHiU) hz⟩)
  have hdL : ∀ y ∈ L, d * y * d⁻¹ ∈ L := by
    intro y hy
    exact (Subgroup.mem_normalizer_iff.mp
      ((D14.le_normalizer_of_isNormalIn (H := H) (U := U) hstep.2.1) hdH) y).mp hy
  have hnc : ¬ IsCentralStep H L K := by
    intro hc
    have hcomm : d * x * d⁻¹ * x⁻¹ ∈ L := hc d hdH x hxK
    exact hxL (mem_of_comm_mem_of_fixedPointFree hY2 hYab hLoL hxY hdY hdL hdo
      (fun z hz => hfpf z hz) hcomm)
  refine ⟨x, hxY, ?_⟩
  intro hcommLo
  apply hxL
  apply htor L K hLoL hKHi hstep hnc x hxK
  · intro s hs
    exact hLoL (hYS s hs x hxY)
  · exact hLoL hcommLo

end CFSG.Quasithin.Stroth


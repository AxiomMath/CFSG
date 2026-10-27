module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixTwoComm
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixHall

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem le_sup_zpowers_of_relIndex_eq_two {L K : Subgroup G} (hLK : L ≤ K)
    (h : L.relIndex K = 2) {a : G} (haK : a ∈ K) (haL : a ∉ L) :
    K ≤ L ⊔ Subgroup.zpowers a := by
  intro x hxK
  have hKindex : (L.subgroupOf K).index = 2 := h
  by_cases hxL : x ∈ L
  · exact Subgroup.mem_sup_left hxL
  · have hmul := Subgroup.mul_mem_iff_of_index_two (H := L.subgroupOf K) hKindex
      (a := (⟨x, hxK⟩ : K)) (b := (⟨a, haK⟩ : K))
    have hxa : x * a ∈ L := by
      have : (⟨x, hxK⟩ : K) * (⟨a, haK⟩ : K) ∈ L.subgroupOf K := by
        rw [hmul]
        exact ⟨fun hx' => absurd (Subgroup.mem_subgroupOf.mp hx') hxL,
          fun ha' => absurd (Subgroup.mem_subgroupOf.mp ha') haL⟩
      exact Subgroup.mem_subgroupOf.mp this
    have hmem : (x * a) * a⁻¹ ∈ L ⊔ Subgroup.zpowers a :=
      (L ⊔ Subgroup.zpowers a).mul_mem (Subgroup.mem_sup_left hxa)
        (Subgroup.mem_sup_right ((Subgroup.zpowers a).inv_mem (Subgroup.mem_zpowers a)))
    rwa [show (x * a) * a⁻¹ = x by group] at hmem

private theorem relIndex_sup_of_le_normalizer {H N : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (N : Set G)) : N.relIndex (H ⊔ N) = N.relIndex H := by
  haveI := Subgroup.normal_subgroupOf_of_le_normalizer hH
  haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hH
  exact (Nat.card_congr
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hH).toEquiv).symm

structure IsHallCompl (V H E J X Y : Subgroup G) : Prop where
  iSub_le : iSub V H E ≤ Y
  le_X : Y ≤ X
  inf_J : Y ⊓ J = iSub V H E
  sup_J : Y ⊔ J = X

variable {V H E J A X : Subgroup G} [(J.subgroupOf X).Normal]

theorem Hyp76.exists_hallCompl (h : Hyp76 V H E J A X) :
    ∃ Y : Subgroup G, IsHallCompl V H E J X Y := by
  have hXn : X ≤ Subgroup.normalizer (J : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le_X).1 inferInstance
  have hJ2 : IsPGroup 2 J :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H).to_le h.le_pCore
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hJ2
  have hcop : Nat.Coprime (Nat.card J) (J.relIndex X) := by
    rw [hk]
    exact (Nat.coprime_two_right.mpr h.relIndex_odd).symm.pow_left k
  obtain ⟨S, hSX, hSinf, hSsup, -⟩ :=
    CFSG.Walter.W67.Sec6.exists_complement_in h.le_X hXn hcop
  have hIleJ : iSub V H E ≤ J := h.iSub_le
  have hIleH : iSub V H E ≤ H := by
    refine iSup_le fun W => iSup_le fun _ => ?_
    exact inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hSnormI : S ≤ Subgroup.normalizer ((iSub V H E : Subgroup G) : Set G) :=
    (hSX.trans h.X_le_H).trans
      (le_normalizer_of_subgroupOf_normal hIleH (iSub_subgroupOf_normal h.le_H h.normal_E))
  refine ⟨S ⊔ iSub V H E, le_sup_right, sup_le hSX (hIleJ.trans h.le_X), ?_, ?_⟩
  · refine le_antisymm ?_ (le_inf le_sup_right hIleJ)
    intro y hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hySI, hyJ⟩ := hy
    have hySI' : y ∈ (↑S : Set G) * (↑(iSub V H E) : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right S (iSub V H E) hSnormI]
      exact hySI
    rw [Set.mem_mul] at hySI'
    obtain ⟨s, hsS, i, hiI, hsi⟩ := hySI'
    have hyJ' : s * i ∈ J := by rw [hsi]; exact hyJ
    have hsJ : s ∈ J := by
      have hmem : (s * i) * i⁻¹ ∈ J := J.mul_mem hyJ' (J.inv_mem (hIleJ hiI))
      rwa [show (s * i) * i⁻¹ = s by group] at hmem
    have hsbot : s = 1 := by
      have : s ∈ (⊥ : Subgroup G) := by
        rw [← hSinf]
        exact ⟨hsJ, hsS⟩
      simpa using this
    rw [← hsi, hsbot, one_mul]
    exact hiI
  · rw [sup_assoc, sup_eq_right.mpr hIleJ, sup_comm S J]
    exact hSsup

theorem Hyp76.relIndex_odd_of_isHallCompl (h : Hyp76 V H E J A X) {Y : Subgroup G}
    (hY : IsHallCompl V H E J X Y) {W : Subgroup G} (hIW : iSub V H E ≤ W) (hWY : W ≤ Y) :
    Odd ((iSub V H E).relIndex W) := by
  have hXnormJ : X ≤ Subgroup.normalizer (J : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le_X).1 inferInstance
  have hYN : Y ≤ Subgroup.normalizer (J : Set G) := hY.le_X.trans hXnormJ
  have h1 : J.relIndex (Y ⊔ J) = J.relIndex Y := relIndex_sup_of_le_normalizer hYN
  have h2 : J.relIndex X = J.relIndex Y := by
    rw [← hY.sup_J]
    exact h1
  have h3 : J.relIndex Y = (iSub V H E).relIndex Y := by
    rw [← Subgroup.inf_relIndex_left Y J, hY.inf_J]
  have hIYodd : Odd ((iSub V H E).relIndex Y) := by
    rw [← h3, ← h2]
    exact h.relIndex_odd
  have hmul : (iSub V H E).relIndex W * W.relIndex Y = (iSub V H E).relIndex Y :=
    Subgroup.relIndex_mul_relIndex (iSub V H E) W Y hIW hWY
  exact hIYodd.of_dvd_nat ⟨W.relIndex Y, hmul.symm⟩

theorem Hyp76.exists_normalizing_member (h : Hyp76 V H E J A X) {Y : Subgroup G}
    (hY : IsHallCompl V H E J X Y) {U : Subgroup G} (hU : U ∈ omegaSet V H E)
    (hUA : U ≤ A ⊔ J) :
    ∃ U' ∈ omegaSet V H E, U' ≤ A ⊔ J ∧ U' ≤ Subgroup.normalizer (Y : Set G) ∧ U ≤ U' ⊔ J := by
  obtain ⟨g, -, -, hUnotO⟩ := mem_omegaSet.mp hU
  have hUJ : ¬ U ≤ J := fun hUJ => hUnotO (hUJ.trans h.le_pCore)
  have hAgen : U = ⨆ U₁ ∈ omegaSet V H E, ⨆ (_ : U₁ ≤ U), U₁ := by
    refine le_antisymm ?_ ?_
    · exact le_iSup_of_le U (le_iSup_of_le hU (le_iSup_of_le le_rfl le_rfl))
    · exact iSup_le fun U₁ => iSup_le fun _ => iSup_le fun hle => hle
  set R : Subgroup G := ⨆ U₁ ∈ omegaSet V H E, ⨆ (_ : U₁ ≤ U ⊔ J),
    ⨆ (_ : U₁ ≤ Subgroup.normalizer (Y : Set G)), U₁ with hR
  have hres : U ⊔ J = R ⊔ J := seven_six_one_hall (V := V) (H := H) (E := E) (J := J)
    (A := U) (X := X) (Y := Y) h.isElemAbelian h.isTI h.isMulCommutative h.le_H h.normal_E
    h.omega_le_H h.le_pCore h.normal_J h.iSub_le h.le_X h.X_le_H
    (hUA.trans h.sup_le_normalizer) h.relIndex_odd h.nilpotent
    (fun a ha hx => h.faithful_sup a (hUA ha) hx) hAgen
    hY.iSub_le hY.le_X hY.inf_J hY.sup_J
  have hex : ∃ U₁ : Subgroup G, U₁ ∈ omegaSet V H E ∧ U₁ ≤ U ⊔ J ∧
      U₁ ≤ Subgroup.normalizer (Y : Set G) ∧ ¬ U₁ ≤ J := by
    by_contra hcon
    have hcon' : ∀ U₁, U₁ ∈ omegaSet V H E → U₁ ≤ U ⊔ J →
        U₁ ≤ Subgroup.normalizer (Y : Set G) → U₁ ≤ J := by
      intro U₁ h1 h2 h3
      by_contra h4
      exact hcon ⟨U₁, h1, h2, h3, h4⟩
    have hRle : R ≤ J := by
      rw [hR]
      refine iSup_le fun U₁ => iSup_le fun hU₁ => iSup_le fun hle => iSup_le fun hN =>
        hcon' U₁ hU₁ hle hN
    have hUleJ : U ⊔ J ≤ J := by
      rw [hres]
      exact sup_le hRle le_rfl
    exact hUJ (le_sup_left.trans hUleJ)
  obtain ⟨U₁, hU₁Ω, hU₁le, hU₁N, hU₁notJ⟩ := hex
  refine ⟨U₁, hU₁Ω, hU₁le.trans (sup_le hUA le_sup_right), hU₁N, ?_⟩
  obtain ⟨u₁, hu₁U₁, hu₁J⟩ := Set.not_subset.mp hU₁notJ
  have hJH : J ≤ H := h.le_pCore.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hUN : U ≤ Subgroup.normalizer (J : Set G) :=
    (h.omega_le_H U hU).trans (le_normalizer_of_subgroupOf_normal hJH h.normal_J)
  have hu₁UJ : u₁ ∈ U ⊔ J := hU₁le hu₁U₁
  have hu₁UJ' : u₁ ∈ (↑U : Set G) * (↑J : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right U J hUN]
    exact hu₁UJ
  rw [Set.mem_mul] at hu₁UJ'
  obtain ⟨u', hu'U, j', hj'J, hu'j'⟩ := hu₁UJ'
  have hu'J : u' ∉ J := by
    intro hu'J
    exact hu₁J (by rw [← hu'j']; exact J.mul_mem hu'J hj'J)
  have hu'U₁J : u' ∈ U₁ ⊔ J := by
    have h' : u' = u₁ * j'⁻¹ := by rw [← hu'j']; group
    rw [h']
    exact (U₁ ⊔ J).mul_mem (Subgroup.mem_sup_left hu₁U₁)
      (Subgroup.mem_sup_right (J.inv_mem hj'J))
  have hUJ2 : (U ⊓ J).relIndex U = 2 := by
    rw [Subgroup.inf_relIndex_left]
    exact (h.relIndex_eq_two hU hUA).1
  have hsplit : U ≤ (U ⊓ J) ⊔ Subgroup.zpowers u' :=
    le_sup_zpowers_of_relIndex_eq_two inf_le_left hUJ2 hu'U
      (fun hmem => hu'J (Subgroup.mem_inf.mp hmem).2)
  exact hsplit.trans (sup_le (inf_le_right.trans le_sup_right)
    (Subgroup.zpowers_le.mpr hu'U₁J))

theorem Hyp76.exists_normalizing_rep (h : Hyp76 V H E J A X) {Y : Subgroup G}
    (hY : IsHallCompl V H E J X Y) {d : G} (hd : d ∈ dSetIn V H E J A) :
    ∃ U' ∈ omegaSet V H E, U' ≤ A ⊔ J ∧
      ∃ d₁ ∈ U', d₁ ∉ J ∧ d₁ ∈ Subgroup.normalizer (Y : Set G) ∧ d⁻¹ * d₁ ∈ J := by
  obtain ⟨U, hU, hUA, hdU, hdJ⟩ := hd
  obtain ⟨U', hU'Ω, hU'A, hU'N, hUleU'J⟩ := h.exists_normalizing_member hY hU hUA
  have hJH : J ≤ H := h.le_pCore.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hU'NJ : U' ≤ Subgroup.normalizer (J : Set G) :=
    (h.omega_le_H U' hU'Ω).trans (le_normalizer_of_subgroupOf_normal hJH h.normal_J)
  have hdU'J : d ∈ U' ⊔ J := hUleU'J hdU
  have hdU'J' : d ∈ (↑U' : Set G) * (↑J : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right U' J hU'NJ]
    exact hdU'J
  rw [Set.mem_mul] at hdU'J'
  obtain ⟨d₁, hd₁U', j, hjJ, hd₁j⟩ := hdU'J'
  have hd₁J : d₁ ∉ J := by
    intro hd₁J
    exact hdJ (by rw [← hd₁j]; exact J.mul_mem hd₁J hjJ)
  refine ⟨U', hU'Ω, hU'A, d₁, hd₁U', hd₁J, hU'N hd₁U', ?_⟩
  rw [← hd₁j, show (d₁ * j)⁻¹ * d₁ = j⁻¹ by group]
  exact J.inv_mem hjJ

end CFSG.LocalAnalysis.WeakClosure81

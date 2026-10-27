module

public import CFSG.RankThree.GF2n.Parrott.Parrott77Lemma6
public import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem mem_zpowers_cases {z g : G} (hz : orderOf z = 2) (hg : g ∈ zpowers z) :
    g = 1 ∨ g = z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
  have key := zpow_mod_orderOf z k
  have h2 : k % (orderOf z : ℤ) = 0 ∨ k % (orderOf z : ℤ) = 1 := by
    rw [hz]
    exact Int.emod_two_eq_zero_or_one k
  rcases h2 with h | h
  · left
    rw [← key, h, zpow_zero]
  · right
    rw [← key, h, zpow_one]

private structure Hyp (z t : G) (J : Subgroup G) : Prop where
  hz : orderOf z = 2
  hJdef : J = inSubgroup (pCore 2) (centralizer ({z} : Set G))
  hJ : IsExtraspecial2 J
  hCH : centralizer ({z} : Set G) ⊓ centralizer (J : Set G) = zpowers z
  ht : orderOf t = 2
  htJ : t ∈ J
  htz : t ∉ zpowers z

namespace Hyp

variable {z t : G} {J : Subgroup G}

omit [Finite G] in
private theorem zz (h : Hyp z t J) : z * z = 1 := by
  rw [← pow_two, ← h.hz, pow_orderOf_eq_one]

omit [Finite G] in
private theorem tt (h : Hyp z t J) : t * t = 1 := by
  rw [← pow_two, ← h.ht, pow_orderOf_eq_one]

omit [Finite G] in
private theorem z1 (h : Hyp z t J) : z ≠ 1 := by
  intro h1
  have := h.hz
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

omit [Finite G] in
private theorem t1 (h : Hyp z t J) : t ≠ 1 := fun h1 => h.htz (h1 ▸ one_mem _)

omit [Finite G] in
private theorem tz_ne (h : Hyp z t J) : t ≠ z := fun h1 => h.htz (h1 ▸ mem_zpowers z)

omit [Finite G] in
private theorem zJ (h : Hyp z t J) : z ∈ J := h.hJdef ▸ mem_inSubgroup_pCore_centralizer_self h.hz

omit [Finite G] in
private theorem JH (h : Hyp z t J) : J ≤ centralizer ({z} : Set G) :=
  h.hJdef ▸ Subgroup.map_subtype_le _

omit [Finite G] in
private theorem normalizes (h : Hyp z t J) : centralizer ({z} : Set G) ≤ normalizer (J : Set G) :=
  h.hJdef ▸ centralizer_le_normalizer_inSubgroup_pCore z

omit [Finite G] in
private theorem zc (_h : Hyp z t J) {y : G} (hy : y ∈ centralizer ({z} : Set G)) : y * z = z * y :=
  mem_centralizer_singleton_iff.mp hy

omit [Finite G] in
private theorem tz (h : Hyp z t J) : t * z = z * t := h.zc (h.JH h.htJ)

private theorem hZ (h : Hyp z t J) : (center J).map J.subtype = zpowers z := by
  have hcard : Nat.card ((center J).map J.subtype) = 2 := by
    rw [← h.hJ.2.1]; exact h.hJ.2.2
  have hle : zpowers z ≤ (center J).map J.subtype := by
    rw [zpowers_le]
    refine ⟨⟨z, h.zJ⟩, mem_center_iff.mpr fun g => ?_, rfl⟩
    exact Subtype.ext (h.zc (h.JH g.2))
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, Nat.card_zpowers, h.hz])).symm

private theorem comm (h : Hyp z t J) {a b : G} (ha : a ∈ J) (hb : b ∈ J) :
    a * b = b * a ∨ a * b = z * (b * a) := by
  have hmem : ⁅a, b⁆ ∈ zpowers z := by
    rw [← h.hZ, ← h.hJ.2.1]
    exact Subgroup.commutator_mem_commutator ha hb
  rcases mem_zpowers_cases h.hz hmem with h1 | h1
  · exact Or.inl (commutatorElement_eq_one_iff_mul_comm.mp h1)
  · right
    rw [commutatorElement_def] at h1
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = z * (b * a) := by rw [h1]

private theorem central (h : Hyp z t J) {y : G} (hy : y ∈ J) (hc : ∀ b ∈ J, y * b = b * y) :
    y = 1 ∨ y = z := by
  have hmem : y ∈ zpowers z := by
    rw [← h.hZ]
    refine ⟨⟨y, hy⟩, mem_center_iff.mpr fun g => ?_, rfl⟩
    exact Subtype.ext (hc g g.2).symm
  exact mem_zpowers_cases h.hz hmem

end Hyp

private def E4 (z t w : G) : Prop := w = 1 ∨ w = z ∨ w = t ∨ w = z * t

namespace Hyp

variable {z t : G} {J : Subgroup G}

private theorem exists_j0 (h : Hyp z t J) : ∃ j₀ ∈ J, j₀ * t = z * (t * j₀) := by
  by_contra hne
  push Not at hne
  have hall : ∀ b ∈ J, t * b = b * t := by
    intro b hb
    rcases h.comm hb h.htJ with h1 | h1
    · exact h1.symm
    · exact absurd h1 (hne b hb)
  rcases h.central h.htJ hall with h1 | h1
  · exact h.t1 h1
  · exact h.tz_ne h1

private theorem relIndex_centralizer_t (h : Hyp z t J) :
    (centralizer ({t} : Set G)).relIndex J = 2 := by
  obtain ⟨j₀, hj₀, hj⟩ := h.exists_j0
  have hz1 := h.z1
  have hzc : ∀ y ∈ J, y * z = z * y := fun y hy => h.zc (h.JH hy)
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨j₀, hj₀⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, mem_centralizer_singleton_iff]
  have hbz := hzc b b.2
  rcases h.comm b.2 h.htJ with h1 | h1
  · refine Or.inr ⟨h1, fun h2 => hz1 ?_⟩
    have hL : ((b : G) * j₀) * t = z * (t * ((b : G) * j₀)) := by
      calc ((b : G) * j₀) * t = b * (j₀ * t) := by rw [mul_assoc]
        _ = b * (z * (t * j₀)) := by rw [hj]
        _ = (b * z) * (t * j₀) := by rw [mul_assoc]
        _ = (z * b) * (t * j₀) := by rw [hbz]
        _ = z * ((b * t) * j₀) := by group
        _ = z * ((t * b) * j₀) := by rw [h1]
        _ = z * (t * ((b : G) * j₀)) := by group
    rw [hL] at h2
    exact mul_eq_right.mp h2
  · refine Or.inl ⟨?_, fun h2 => hz1 ?_⟩
    · calc ((b : G) * j₀) * t = b * (j₀ * t) := by rw [mul_assoc]
        _ = b * (z * (t * j₀)) := by rw [hj]
        _ = (b * z) * (t * j₀) := by rw [mul_assoc]
        _ = (z * b) * (t * j₀) := by rw [hbz]
        _ = z * ((b * t) * j₀) := by group
        _ = z * ((z * (t * b)) * j₀) := by rw [h1]
        _ = (z * z) * ((t * b) * j₀) := by group
        _ = t * ((b : G) * j₀) := by rw [h.zz]; group
    · rw [h2] at h1
      exact mul_eq_right.mp h1.symm

end Hyp

namespace Hyp

variable {z t : G} {J : Subgroup G}

omit [Finite G] in
private theorem j0_not_mem (h : Hyp z t J) {j₀ : G} (hj : j₀ * t = z * (t * j₀)) :
    j₀ ∉ centralizer ({t} : Set G) := by
  intro hmem
  have h1 : j₀ * t = t * j₀ := mem_centralizer_singleton_iff.mp hmem
  rw [h1] at hj
  exact h.z1 (mul_eq_right.mp hj.symm)

private theorem inv_mul_mem (h : Hyp z t J) {j₀ b : G} (hj₀ : j₀ ∈ J) (hb : b ∈ J)
    (hj₀t : j₀ ∉ centralizer ({t} : Set G)) (hbt : b ∉ centralizer ({t} : Set G)) :
    j₀⁻¹ * b ∈ centralizer ({t} : Set G) := by
  have hD : ((centralizer ({t} : Set G)).subgroupOf J).index = 2 := h.relIndex_centralizer_t
  have key := (Subgroup.mul_mem_iff_of_index_two hD (a := (⟨j₀, hj₀⟩ : J)⁻¹)
    (b := ⟨b, hb⟩)).mpr (by
      rw [inv_mem_iff]
      simp only [Subgroup.mem_subgroupOf]
      exact ⟨fun h1 => absurd h1 hj₀t, fun h1 => absurd h1 hbt⟩)
  simpa [Subgroup.mem_subgroupOf] using key

private theorem central_of_comm_inf (h : Hyp z t J) {j₀ y : G} (hj₀ : j₀ ∈ J)
    (hj₀t : j₀ ∉ centralizer ({t} : Set G)) (hy : y ∈ J)
    (hyA : ∀ b ∈ J ⊓ centralizer ({t} : Set G), y * b = b * y) (hyj : y * j₀ = j₀ * y) :
    y = 1 ∨ y = z := by
  refine h.central hy fun b hb => ?_
  by_cases hbt : b ∈ centralizer ({t} : Set G)
  · exact hyA b ⟨hb, hbt⟩
  · have hm : j₀⁻¹ * b ∈ centralizer ({t} : Set G) := h.inv_mul_mem hj₀ hb hj₀t hbt
    have hmJ : j₀⁻¹ * b ∈ J := J.mul_mem (J.inv_mem hj₀) hb
    have h1 := hyA _ ⟨hmJ, hm⟩
    calc y * b = y * j₀ * (j₀⁻¹ * b) := by group
      _ = j₀ * y * (j₀⁻¹ * b) := by rw [hyj]
      _ = j₀ * (y * (j₀⁻¹ * b)) := by rw [mul_assoc]
      _ = j₀ * ((j₀⁻¹ * b) * y) := by rw [h1]
      _ = b * y := by group

private theorem E4_of_center_inf (h : Hyp z t J) {a : G}
    (ha : a ∈ J ⊓ centralizer ({t} : Set G))
    (hc : ∀ b ∈ J ⊓ centralizer ({t} : Set G), a * b = b * a) : E4 z t a := by
  obtain ⟨j₀, hj₀, hj⟩ := h.exists_j0
  have hnot := h.j0_not_mem hj
  have haJ : a ∈ J := ha.1
  rcases h.comm haJ hj₀ with h1 | h1
  · rcases h.central_of_comm_inf hj₀ hnot haJ hc h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl h2)
  · have hy : a * t ∈ J := J.mul_mem haJ h.htJ
    have hyA : ∀ b ∈ J ⊓ centralizer ({t} : Set G), (a * t) * b = b * (a * t) := by
      intro b hb
      have hbt : b * t = t * b := mem_centralizer_singleton_iff.mp hb.2
      calc (a * t) * b = a * (t * b) := by rw [mul_assoc]
        _ = a * (b * t) := by rw [hbt]
        _ = (a * b) * t := by rw [mul_assoc]
        _ = (b * a) * t := by rw [hc b hb]
        _ = b * (a * t) := by rw [mul_assoc]
    have htj : t * j₀ = z * (j₀ * t) := by
      calc t * j₀ = (z * z) * (t * j₀) := by rw [h.zz, one_mul]
        _ = z * (z * (t * j₀)) := by rw [mul_assoc]
        _ = z * (j₀ * t) := by rw [← hj]
    have hza : a * z = z * a := h.zc (h.JH haJ)
    have hyj : (a * t) * j₀ = j₀ * (a * t) := by
      calc (a * t) * j₀ = a * (t * j₀) := by rw [mul_assoc]
        _ = a * (z * (j₀ * t)) := by rw [htj]
        _ = (a * z) * (j₀ * t) := by rw [mul_assoc]
        _ = (z * a) * (j₀ * t) := by rw [hza]
        _ = z * ((a * j₀) * t) := by group
        _ = z * ((z * (j₀ * a)) * t) := by rw [h1]
        _ = (z * z) * (j₀ * (a * t)) := by group
        _ = j₀ * (a * t) := by rw [h.zz, one_mul]
    have hat1 : a = (a * t) * t := by rw [mul_assoc, h.tt, mul_one]
    rcases h.central_of_comm_inf hj₀ hnot hy hyA hyj with h2 | h2
    · refine Or.inr (Or.inr (Or.inl ?_))
      rw [hat1, h2, one_mul]
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [hat1, h2]

omit [Finite G] in
private theorem E4_mem_inf (h : Hyp z t J) {w : G} (hw : E4 z t w) :
    w ∈ J ⊓ centralizer ({t} : Set G) := by
  have hzt : z ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr h.tz.symm
  have htt : t ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  rcases hw with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact ⟨h.zJ, hzt⟩
  · exact ⟨h.htJ, htt⟩
  · exact ⟨J.mul_mem h.zJ h.htJ, mul_mem hzt htt⟩

omit [Finite G] in
private theorem E4_comm (h : Hyp z t J) {w c : G} (hw : E4 z t w)
    (hc : c ∈ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) : c * w = w * c := by
  have h1 : c * z = z * c := mem_centralizer_singleton_iff.mp hc.1
  have h2 : c * t = t * c := mem_centralizer_singleton_iff.mp hc.2
  rcases hw with rfl | rfl | rfl | rfl
  · rw [mul_one, one_mul]
  · exact h1
  · exact h2
  · calc c * (z * t) = (c * z) * t := by rw [mul_assoc]
      _ = (z * c) * t := by rw [h1]
      _ = z * (c * t) := by rw [mul_assoc]
      _ = z * (t * c) := by rw [h2]
      _ = (z * t) * c := by rw [mul_assoc]

omit [Finite G] in
private theorem E4_sq (h : Hyp z t J) {w : G} (hw : E4 z t w) : w * w = 1 := by
  rcases hw with rfl | rfl | rfl | rfl
  · rw [one_mul]
  · exact h.zz
  · exact h.tt
  · calc z * t * (z * t) = z * (t * z) * t := by group
      _ = z * (z * t) * t := by rw [h.tz]
      _ = (z * z) * (t * t) := by group
      _ = 1 := by rw [h.zz, h.tt, one_mul]

omit [Finite G] in
private theorem inf_normal (h : Hyp z t J) {c a : G}
    (hc : c ∈ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G))
    (ha : a ∈ J ⊓ centralizer ({t} : Set G)) :
    c * a * c⁻¹ ∈ J ⊓ centralizer ({t} : Set G) := by
  refine ⟨(mem_normalizer_iff.mp (h.normalizes hc.1) a).mp ha.1,
    mem_centralizer_singleton_iff.mpr ?_⟩
  have hct : c * t = t * c := mem_centralizer_singleton_iff.mp hc.2
  have hat : a * t = t * a := mem_centralizer_singleton_iff.mp ha.2
  have hct' : c⁻¹ * t = t * c⁻¹ := by
    calc c⁻¹ * t = c⁻¹ * (t * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * t) * c⁻¹ := by rw [hct]
      _ = t * c⁻¹ := by group
  calc c * a * c⁻¹ * t = c * a * (c⁻¹ * t) := by rw [mul_assoc]
    _ = c * a * (t * c⁻¹) := by rw [hct']
    _ = c * (a * t) * c⁻¹ := by group
    _ = c * (t * a) * c⁻¹ := by rw [hat]
    _ = (c * t) * a * c⁻¹ := by group
    _ = (t * c) * a * c⁻¹ := by rw [hct]
    _ = t * (c * a * c⁻¹) := by group

end Hyp

private def IsMaxTwo (K T : Subgroup G) : Prop :=
  T ≤ K ∧ IsPGroup 2 T ∧ ∀ S : Subgroup G, S ≤ K → IsPGroup 2 S → T ≤ S → S = T

omit [Finite G] in
private theorem le_of_normal {K T V : Subgroup G} (hT : IsMaxTwo K T) (hVK : V ≤ K)
    (hVn : ∀ k ∈ K, ∀ v ∈ V, k * v * k⁻¹ ∈ V) (hV : IsPGroup 2 V) : V ≤ T := by
  have hTn : T ≤ normalizer (V : Set G) := by
    intro k hk
    rw [mem_normalizer_iff]
    intro v
    refine ⟨fun hv => hVn k (hT.1 hk) v hv, fun hv => ?_⟩
    have := hVn k⁻¹ (K.inv_mem (hT.1 hk)) _ hv
    rwa [show k⁻¹ * (k * v * k⁻¹) * k⁻¹⁻¹ = v by group] at this
  have hsup : IsPGroup 2 (T ⊔ V : Subgroup G) := hT.2.1.to_sup_of_normal_right' hV hTn
  have heq := hT.2.2 (T ⊔ V) (sup_le hT.1 hVK) hsup le_sup_left
  exact heq ▸ le_sup_right

namespace Hyp

variable {z t : G} {J : Subgroup G}

omit [Finite G] in
private theorem isPGroup_inf (h : Hyp z t J) : IsPGroup 2 (J ⊓ centralizer ({t} : Set G) :
    Subgroup G) := h.hJ.1.to_le inf_le_left

omit [Finite G] in
private theorem inf_le_C (h : Hyp z t J) :
    J ⊓ centralizer ({t} : Set G) ≤ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) :=
  fun _ hy => ⟨h.JH hy.1, hy.2⟩

omit [Finite G] in
private theorem inf_le_T (h : Hyp z t J) {T : Subgroup G}
    (hT : IsMaxTwo (centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) T) :
    J ⊓ centralizer ({t} : Set G) ≤ T :=
  le_of_normal hT h.inf_le_C (fun _ hc _ ha => h.inf_normal hc ha) h.isPGroup_inf

private theorem E4_of_central_T (h : Hyp z t J) {T : Subgroup G}
    (hT : IsMaxTwo (centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) T)
    {w : G} (hwT : w ∈ T) (hw2 : w * w = 1) (hwc : ∀ s ∈ T, w * s = s * w) : E4 z t w := by
  have hAT := h.inf_le_T hT
  have hwC := hT.1 hwT
  by_cases hwJ : w ∈ J
  · exact h.E4_of_center_inf ⟨hwJ, hwC.2⟩ fun b hb => hwc b (hAT hb)
  · exfalso
    have hcomm : ∀ a ∈ J ⊓ centralizer ({t} : Set G), a ∈ centralizer ({w} : Set G) := by
      intro a ha
      exact mem_centralizer_singleton_iff.mpr (hwc a (hAT ha)).symm
    have hdvd : (centralizer ({w} : Set G)).relIndex J ∣ 2 := by
      have hle : centralizer ({t} : Set G) ⊓ J ≤ centralizer ({w} : Set G) ⊓ J :=
        fun a ha => ⟨hcomm a ⟨ha.2, ha.1⟩, ha.2⟩
      have h1 := Subgroup.relIndex_dvd_of_le_left J hle
      rwa [Subgroup.inf_relIndex_right, Subgroup.inf_relIndex_right,
        h.relIndex_centralizer_t] at h1
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · have hJw : J ≤ centralizer ({w} : Set G) := Subgroup.relIndex_eq_one.mp h1
      have hwcJ : w ∈ centralizer (J : Set G) := by
        rw [mem_centralizer_iff]
        intro j hj
        exact mem_centralizer_singleton_iff.mp (hJw hj)
      have hwmem : w ∈ centralizer ({z} : Set G) ⊓ centralizer (J : Set G) := ⟨hwC.1, hwcJ⟩
      rw [h.hCH] at hwmem
      exact hwJ (zpowers_le.mpr h.zJ hwmem)
    · have hnot := parrott77_lemma6 z J h.hz h.hJdef h.hJ h.hCH hwC.1 hwJ h2
      apply hnot
      rw [pow_two, hw2]
      exact one_mem _

end Hyp

namespace Hyp

variable {z t : G} {J : Subgroup G}

omit [Finite G] in
private theorem E4_iff_mem_sup (h : Hyp z t J) {w : G} :
    E4 z t w ↔ w ∈ zpowers z ⊔ zpowers t := by
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact mem_sup_left (mem_zpowers _)
    · exact mem_sup_right (mem_zpowers _)
    · exact mul_mem_sup (mem_zpowers _) (mem_zpowers _)
  · intro hw
    have hab : ∀ a ∈ zpowers z, ∀ b ∈ zpowers t, Commute a b := by
      intro a ha b hb
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
      obtain ⟨l, rfl⟩ := mem_zpowers_iff.mp hb
      exact (show Commute z t from h.tz.symm).zpow_zpow k l
    obtain ⟨a, ha, b, hb, rfl⟩ := (CFSG.mem_sup_of_commute hab).mp hw
    rcases mem_zpowers_cases h.hz ha with ha' | ha' <;>
      rcases mem_zpowers_cases h.ht hb with hb' | hb' <;> rw [ha', hb']
    · exact Or.inl (one_mul 1)
    · exact Or.inr (Or.inr (Or.inl (one_mul t)))
    · exact Or.inr (Or.inl (mul_one z))
    · exact Or.inr (Or.inr (Or.inr rfl))

end Hyp

theorem parrott77_omega_one_center (z t : G) (J : Subgroup G) (hz : orderOf z = 2)
    (hJdef : J = inSubgroup (pCore 2) (centralizer ({z} : Set G))) (hJ : IsExtraspecial2 J)
    (hCH : centralizer ({z} : Set G) ⊓ centralizer (J : Set G) = zpowers z)
    (ht : orderOf t = 2) (htJ : t ∈ J) (htz : t ∉ zpowers z) {T : Subgroup G}
    (hTle : T ≤ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) (hT2 : IsPGroup 2 T)
    (hTmax : ∀ S : Subgroup G, S ≤ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) →
      IsPGroup 2 S → T ≤ S → S = T) (w : G) :
    (w ∈ T ⊓ centralizer (T : Set G) ∧ w * w = 1) ↔ w ∈ zpowers z ⊔ zpowers t := by
  have h : Hyp z t J := ⟨hz, hJdef, hJ, hCH, ht, htJ, htz⟩
  have hT : IsMaxTwo (centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)) T :=
    ⟨hTle, hT2, hTmax⟩
  rw [← h.E4_iff_mem_sup]
  constructor
  · rintro ⟨⟨hwT, hwc⟩, hw2⟩
    exact h.E4_of_central_T hT hwT hw2 fun s hs => (mem_centralizer_iff.mp hwc s hs).symm
  · intro hw
    exact ⟨⟨h.inf_le_T hT (h.E4_mem_inf hw),
      mem_centralizer_iff.mpr fun s hs => h.E4_comm hw (hTle hs)⟩, h.E4_sq hw⟩

end CFSG.RankThree.GF2n.Parrott

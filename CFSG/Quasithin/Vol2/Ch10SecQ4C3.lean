module

public import CFSG.Quasithin.Vol2.Ch10SecQ4C2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem conj_mem_centralizer {S : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) (hc : c ∈ Subgroup.centralizer (S : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro s hs
  have hs' : g⁻¹ * s * g ∈ S := (Subgroup.mem_normalizer_iff''.mp hg s).mp hs
  have key := hc _ hs'
  calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [key]
    _ = g * c * g⁻¹ * s := by group

theorem le_normalizer_zpowers {X : Subgroup G} {w : G}
    (h : ∀ s ∈ X, s * w * s⁻¹ ∈ Subgroup.zpowers w) :
    X ≤ Subgroup.normalizer ((Subgroup.zpowers w : Subgroup G) : Set G) := by
  have hmap : ∀ s ∈ X, ∀ y ∈ Subgroup.zpowers w, s * y * s⁻¹ ∈ Subgroup.zpowers w := by
    intro s hs y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (h s hs)
    refine Subgroup.mem_zpowers_iff.mpr ⟨m * k, ?_⟩
    rw [zpow_mul, hm, ← conj_zpow]
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact hmap s hs y
  · intro hy
    have := hmap s⁻¹ (X.inv_mem hs) _ hy
    simpa [mul_assoc] using this

theorem orderOf_conj' (s z : G) : orderOf (s * z * s⁻¹) = orderOf z :=
  (SemiconjBy.orderOf_eq s (show s * z = s * z * s⁻¹ * s by group)).symm

theorem false_of_isHat [Finite G] {L J X T₁ P : Subgroup G} {t z z₀ x : G}
    (hhat : IsHat (↥J ⧸ CFSG.pCore 2 ↥J) ↥(alternatingGroup (Fin 7)))
    (hz₀J : z₀ ∈ J) (hz₀C : z₀ ∈ Subgroup.centralizer (J : Set G)) (hz₀ : orderOf z₀ = 3)
    (h3J : ∀ y ∈ X, orderOf y = 3 → y ∈ J) (hT₁J : T₁ ≤ Subgroup.normalizer (J : Set G))
    (hA : IsAltType L 5) (hP : IsSylowTwoOf P L) (hPT : ∀ s ∈ P, t⁻¹ * s * t ∈ T₁)
    (hLJ : L ≤ J) (hxL : x ∈ L) (hxo : orderOf x = 5) (hzX : z ∈ X) (hzo : orderOf z = 3)
    (hzL : z ∈ Subgroup.centralizer (L : Set G)) (hzt : t * z * t⁻¹ ∈ L) : False := by
  have hzJ : z ∈ J := h3J z hzX hzo
  have hxJ : x ∈ J := hLJ hxL
  have hzz₀ : z ∈ Subgroup.zpowers z₀ := mem_zpowers_of_isHat hhat hz₀J hz₀C hz₀ hxJ hzJ hxo hzo
    (Subgroup.mem_centralizer_iff.mp hzL x hxL)
  have hzeq : Subgroup.zpowers z = Subgroup.zpowers z₀ :=
    Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hzz₀)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hz₀, hzo])
  have hzC : z ∈ Subgroup.centralizer (J : Set G) := (Subgroup.zpowers_le.mpr hz₀C) hzz₀
  have hT₁z : ∀ s ∈ T₁, s * z * s⁻¹ ∈ Subgroup.zpowers z := by
    intro s hs
    have hsJ := hT₁J hs
    have h1 : s * z * s⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hsJ z).mp hzJ
    have h2 : s * z * s⁻¹ ∈ Subgroup.centralizer (J : Set G) := conj_mem_centralizer hsJ hzC
    have h3 : orderOf (s * z * s⁻¹) = 3 := by rw [orderOf_conj']; exact hzo
    rw [hzeq]
    exact mem_zpowers_of_isHat hhat hz₀J hz₀C hz₀ hxJ h1 hxo h3
      (Subgroup.mem_centralizer_iff.mp h2 x hxJ)
  have hPn : P ≤ Subgroup.normalizer
      ((Subgroup.zpowers (t * z * t⁻¹) : Subgroup G) : Set G) := by
    apply le_normalizer_zpowers
    intro s hs
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hT₁z _ (hPT s hs))
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    rw [conj_zpow, hm]
    group
  exact false_of_le_normalizer_zpowers hA hP hzt (by rw [orderOf_conj']; exact hzo) hPn

@[expose] def threeCycle5 : ↥(alternatingGroup (Fin 5)) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 0 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

theorem orderOf_threeCycle5 : orderOf threeCycle5 = 3 := by
  rw [← Subgroup.orderOf_coe]
  exact (Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).orderOf

theorem exists_elemAbelian_gt_three [Finite G] {J K : Subgroup G} (hKJ : K ≤ J) (hA : IsAltType K 5)
    {z₀ : G} (hz₀J : z₀ ∈ J) (hz₀C : z₀ ∈ Subgroup.centralizer (J : Set G))
    (hz₀ : orderOf z₀ = 3) :
    ∃ E : Subgroup G, E ≤ J ∧ IsElemAbelian 3 E ∧ 3 < Nat.card E := by
  obtain ⟨α, hαs, hαk, -⟩ := hA
  obtain ⟨k, hk⟩ := hαs threeCycle5
  have hy'3 : orderOf (k ^ (orderOf k / 3)) = 3 := by
    have hdvd : 3 ∣ orderOf k := orderOf_threeCycle5 ▸ hk ▸ orderOf_map_dvd α k
    exact orderOf_pow_orderOf_div (orderOf_pos k).ne' hdvd
  set y' := k ^ (orderOf k / 3) with hy'
  have hy3 : orderOf (y' : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hy'3
  have hyJ : (y' : G) ∈ J := hKJ y'.2
  have hyz : (y' : G) ∉ Subgroup.zpowers z₀ := by
    intro hyz
    have hyC : (y' : G) ∈ Subgroup.centralizer (J : Set G) :=
      (Subgroup.zpowers_le.mpr hz₀C) hyz
    have hcen : α y' = 1 := alt5_center _ (fun h => by
      obtain ⟨l, rfl⟩ := hαs h
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyC l (hKJ l.2)).symm)
    have := orderOf_alt_eq_three hαk hy'3
    rw [hcen, orderOf_one] at this
    omega
  have hzy : z₀ * y' = y' * z₀ := (Subgroup.mem_centralizer_iff.mp hz₀C _ hyJ).symm
  have hpair : ({z₀, (y' : G)} : Set G).Pairwise Commute := by
    intro a ha b hb _
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Commute.refl _
    · exact hzy
    · exact hzy.symm
    · exact Commute.refl _
  set E := Subgroup.closure ({z₀, (y' : G)} : Set G) with hE
  have hEcomm : IsMulCommutative ↥E := Subgroup.isMulCommutative_closure hpair
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine ⟨E, ?_, ⟨hEcomm, ?_⟩, ?_⟩
  · rw [hE, Subgroup.closure_le]
    rintro a (rfl | rfl)
    · exact hz₀J
    · exact hyJ
  · intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with rfl | rfl
      · exact hz₀ ▸ pow_orderOf_eq_one _
      · exact hy3 ▸ pow_orderOf_eq_one _
    | one => exact one_pow 3
    | mul a b ha hb iha ihb =>
      rw [(Commute.mul_pow (hEc a ha b hb) 3), iha, ihb, one_mul]
    | inv a _ ih => rw [inv_pow, ih, inv_one]
  · have hlt : Subgroup.zpowers z₀ < E := by
      refine lt_of_le_of_ne ((Subgroup.zpowers_le).mpr (Subgroup.subset_closure (by simp))) ?_
      intro heq
      apply hyz
      rw [heq]
      exact Subgroup.subset_closure (by simp)
    have := Subgroup.card_lt_of_lt hlt
    rwa [Nat.card_zpowers, hz₀] at this

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

module

import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Source.PiecesContradiction
public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

@[expose] def Item3_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → CFSG.Assembly.IsCharTwoType G →
    ∀ M : Subgroup G, CFSG.IsMaximalTwoLocal M → ∀ V : Subgroup G,
      Maximal (fun W : Subgroup G => W ≤ M ∧ M ≤ Subgroup.normalizer (W : Set G) ∧
        CFSG.Assembly.IsElemAbelian 2 W) V →
      (∀ g : G, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V ⊓ V.map (MulAut.conj g).toMonoidHom = V) →
      CFSG.Assembly.InCatalog G

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_fourGroups_of_moved {A H V : Subgroup G} {a w : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hHA : H ≤ A) (haA : a ∈ A)
    (hAHa : A ≤ H ⊔ Subgroup.zpowers a) (hV : CFSG.Assembly.IsElemAbelian 2 V)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hwV : w ∈ V)
    (hwH : w ∈ Subgroup.centralizer (H : Set G)) (haw : a * w * a⁻¹ ≠ w) :
    ∃ U ∈ fourGroups A, U ≤ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha3 : a ^ 3 = 1 := hA.2 a haA
  have hconj : ∀ x ∈ V, a * x * a⁻¹ ∈ V := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hAV haA) x).mp hx
  have hcomm : ∀ x ∈ V, ∀ x' ∈ V, x * x' = x' * x := fun x hx x' hx' =>
    congrArg Subtype.val (hV.1.is_comm.comm ⟨x, hx⟩ ⟨x', hx'⟩)
  have hsq : ∀ x ∈ V, x * x = 1 := fun x hx => by rw [← sq]; exact hV.2 x hx
  obtain ⟨w₁, hw₁⟩ : ∃ w₁, w₁ = a * w * a⁻¹ := ⟨_, rfl⟩
  obtain ⟨w₂, hw₂⟩ : ∃ w₂, w₂ = a * w₁ * a⁻¹ := ⟨_, rfl⟩
  rw [← hw₁] at haw
  have hw₁V : w₁ ∈ V := hw₁ ▸ hconj w hwV
  have hw₂V : w₂ ∈ V := hw₂ ▸ hconj w₁ hw₁V
  have haw₂ : a * w₂ * a⁻¹ = w := by
    have h3 : a * (a * a) = 1 := by rw [← pow_three]; exact ha3
    rw [hw₂, hw₁]
    calc a * (a * (a * w * a⁻¹) * a⁻¹) * a⁻¹ = a * (a * a) * w * (a * (a * a))⁻¹ := by group
      _ = w := by rw [h3]; group
  have hw₂w : w₂ ≠ w := by
    intro h
    rw [h, ← hw₁] at haw₂
    exact haw haw₂
  obtain ⟨y, hy⟩ : ∃ y, y = w * w₁ := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = w₁ * w₂ := ⟨_, rfl⟩
  have hyV : y ∈ V := hy ▸ V.mul_mem hwV hw₁V
  have hzV : z ∈ V := hz ▸ V.mul_mem hw₁V hw₂V
  have hy1 : y ≠ 1 := by
    intro h
    apply haw
    calc w₁ = w * w * w₁ := by rw [hsq w hwV, one_mul]
      _ = w * y := by rw [hy, mul_assoc]
      _ = w := by rw [h, mul_one]
  have hay : a * y * a⁻¹ = z := by
    rw [hz, hy, hw₂, hw₁]
    group
  have hz1 : z ≠ 1 := by
    intro h
    apply hy1
    rw [← hay] at h
    calc y = a⁻¹ * (a * y * a⁻¹) * a := by group
      _ = 1 := by rw [h]; group
  have hyz : y ≠ z := by
    intro h
    apply hw₂w
    have h' : w * w₁ = w₂ * w₁ := by rw [← hy, h, hz, hcomm w₁ hw₁V w₂ hw₂V]
    exact (mul_right_cancel h').symm
  have haz : a * z * a⁻¹ = y * z := by
    have h1 : a * z * a⁻¹ = (a * w₁ * a⁻¹) * (a * w₂ * a⁻¹) := by rw [hz]; group
    have h2 : y * z = w * (w₁ * w₁) * w₂ := by rw [hy, hz]; group
    rw [h1, ← hw₂, haw₂, h2, hsq w₁ hw₁V, mul_one, hcomm w hwV w₂ hw₂V]
  have hHyz : ∀ h ∈ H, Commute h y ∧ Commute h z := by
    intro h hh
    have hha : Commute h a := congrArg Subtype.val (hA.1.is_comm.comm ⟨h, hHA hh⟩ ⟨a, haA⟩)
    have hhw : Commute h w := Subgroup.mem_centralizer_iff.mp hwH h hh
    have hh1 : Commute h w₁ := hw₁ ▸ (hha.mul_right hhw).mul_right hha.inv_right
    have hh2 : Commute h w₂ := hw₂ ▸ (hha.mul_right hh1).mul_right hha.inv_right
    exact ⟨hy ▸ hhw.mul_right hh1, hz ▸ hh1.mul_right hh2⟩
  set U := Subgroup.zpowers y ⊔ Subgroup.zpowers z with hU
  have hUV : U ≤ V := sup_le (Subgroup.zpowers_le.mpr hyV) (Subgroup.zpowers_le.mpr hzV)
  have hy2 : y ^ 2 = 1 := hV.2 y hyV
  have hzy : z ∉ Subgroup.zpowers y := by
    intro hzmem
    rcases (Source.mem_zpowers_of_sq_eq_one hy2).mp hzmem with h | h
    · exact hz1 h
    · exact hyz h.symm
  obtain ⟨hUab, hUcard⟩ := Sec5.isElemAbelian_sup_zpowers
    (Sec5.isElemAbelian_of_le hV (Subgroup.zpowers_le.mpr hyV)) hzy (hV.2 z hzV)
    fun x hx => hcomm x (Subgroup.zpowers_le.mpr hyV hx) z hzV
  rw [Nat.card_zpowers, orderOf_eq_prime hy2 hy1] at hUcard
  have hHN : H ≤ Subgroup.normalizer (U : Set G) := by
    intro h hh
    refine Subgroup.centralizer_le_normalizer _ ?_
    have hUC : U ≤ Subgroup.centralizer ({h} : Set G) :=
      sup_le (Subgroup.zpowers_le.mpr
          (Subgroup.mem_centralizer_singleton_iff.mpr (hHyz h hh).1.symm.eq))
        (Subgroup.zpowers_le.mpr
          (Subgroup.mem_centralizer_singleton_iff.mpr (hHyz h hh).2.symm.eq))
    rw [Subgroup.mem_centralizer_iff]
    exact fun u hu => Subgroup.mem_centralizer_singleton_iff.mp (hUC hu)
  have haN : a ∈ Subgroup.normalizer (U : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have hle : U ≤ U.comap (MulAut.conj a).toMonoidHom := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · change a * y * a⁻¹ ∈ U
        rw [hay]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
      · change a * z * a⁻¹ ∈ U
        rw [haz]
        exact U.mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers y))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
    exact hle hn
  exact ⟨U, mem_fourGroups_iff.mpr ⟨hAHa.trans (sup_le hHN (Subgroup.zpowers_le.mpr haN)), hUab,
    hUcard⟩, hUV⟩

theorem exists_mem_fourGroups_le {A V : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hV : CFSG.Assembly.IsElemAbelian 2 V) (hV4 : 4 ≤ Nat.card V)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) : ∃ U ∈ fourGroups A, U ≤ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hV2 : IsPGroup 2 V := Sec5.isPGroup_of_isElemAbelian hV
  set W := V ⊓ Subgroup.centralizer (A : Set G) with hW
  by_cases hW4 : 4 ≤ Nat.card W
  ·
    obtain ⟨k, hk⟩ := (hV2.to_le inf_le_left : IsPGroup 2 W).exists_card_eq
    have hk2 : 2 ≤ k := by
      by_contra h
      have h1 : 2 ^ k ≤ 2 := by
        calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 2 := by norm_num
      rw [← hk] at h1
      omega
    obtain ⟨U', hU'⟩ := Sylow.exists_subgroup_card_pow_prime (G := W) 2 (n := 2)
      (by rw [hk]; exact pow_dvd_pow 2 hk2)
    set U := U'.map W.subtype with hU
    have hUW : U ≤ W := Subgroup.map_subtype_le _
    refine ⟨U, mem_fourGroups_iff.mpr ⟨?_, Sec5.isElemAbelian_of_le hV (hUW.trans inf_le_left),
      ?_⟩, hUW.trans inf_le_left⟩
    · exact (Subgroup.le_centralizer_iff.mp (hUW.trans inf_le_right)).trans
        (Subgroup.centralizer_le_normalizer _)
    · rw [hU, Subgroup.card_map_of_injective W.subtype_injective, hU']
      norm_num
  ·
    push Not at hW4
    have hcop : Nat.Coprime 3 (Nat.card V) := by
      obtain ⟨k, hk⟩ := hV2.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k (by norm_num)
    obtain ⟨H, hHA, hH9, w, hwV, hwH, hwA⟩ : ∃ H : Subgroup G, H ≤ A ∧ Nat.card H = 9 ∧
        ∃ w ∈ V, w ∈ Subgroup.centralizer (H : Set G) ∧
          w ∉ Subgroup.centralizer (A : Set G) := by
      by_contra hno
      push Not at hno
      have hVA : V ≤ Subgroup.centralizer (A : Set G) :=
        Sec5.le_of_forall_inf_centralizer_sub_le (k := 2) Nat.prime_three hA
          (by rw [hA27]; norm_num) hAV hcop fun H hHA hH9 x hx =>
            hno H hHA (by rw [hH9]; norm_num) x hx.1 hx.2
      have hWV : W = V := inf_eq_left.mpr hVA
      rw [hWV] at hW4
      omega
    obtain ⟨a, haA, haw⟩ : ∃ a ∈ A, a * w * a⁻¹ ≠ w := by
      by_contra hno
      push Not at hno
      apply hwA
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      calc a * w = a * w * a⁻¹ * a := by group
        _ = w * a := by rw [hno a ha]
    have haH : a ∉ H := fun haH => haw (by
      rw [Subgroup.mem_centralizer_iff.mp hwH a haH, mul_inv_cancel_right])
    have hle : H ⊔ Subgroup.zpowers a ≤ A := sup_le hHA (Subgroup.zpowers_le.mpr haA)
    have hlt : H < H ⊔ Subgroup.zpowers a := IsConcreteLE.lt_iff_le_and_exists.mpr
      ⟨le_sup_left, a, Subgroup.mem_sup_right (Subgroup.mem_zpowers a), haH⟩
    have hcard := Subgroup.card_lt_of_lt hlt
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hA27] at hdvd
    rw [hH9] at hcard
    have h27 : Nat.card (H ⊔ Subgroup.zpowers a : Subgroup G) = 27 := by
      have hmem : Nat.card (H ⊔ Subgroup.zpowers a : Subgroup G) ∈ Nat.divisors 27 :=
        Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have hdiv : Nat.divisors 27 = {1, 3, 9, 27} := by decide
      rw [hdiv] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      omega
    exact exists_mem_fourGroups_of_moved hA hHA haA
      (Subgroup.eq_of_le_of_card_ge hle (by rw [h27, hA27])).ge hV hAV hwV hwH haw

end CFSG.RankThree.PartTwo.Sec6

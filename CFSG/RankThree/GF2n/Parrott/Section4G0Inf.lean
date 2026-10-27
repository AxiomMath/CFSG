module

public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem inSubgroup_pCore_inf_normal (z : G) {G₀ : Subgroup G} (hG₀ : G₀.Normal) :
    inSubgroup (pCore 2) (H z ⊓ G₀) = J z ⊓ G₀ := by
  have hHN : ∀ x ∈ H z, ∀ y ∈ H z ⊓ G₀, x * y * x⁻¹ ∈ H z ⊓ G₀ := fun x hx y hy =>
    Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy.1) (inv_mem hx),
      hG₀.conj_mem y hy.2 x⟩
  have hnorm : ∀ x ∈ H z, x ∈ normalizer ((H z ⊓ G₀ : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hHN x hx y, fun hy => ?_⟩
    have := hHN x⁻¹ (inv_mem hx) _ hy
    simpa [mul_assoc] using this
  have hJN : H z ≤ normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
  have hJp : IsPGroup 2 (J z) := (pCore_isPGroup (p := 2) (G := ↥(H z))).map (H z).subtype
  apply le_antisymm
  · intro x hx
    have hxH₀ : x ∈ H z ⊓ G₀ := Subgroup.map_subtype_le _ hx
    refine Subgroup.mem_inf.mpr ⟨?_, hxH₀.2⟩
    let P : Subgroup G := inSubgroup (pCore 2) (H z ⊓ G₀)
    have hPH : P ≤ H z := (Subgroup.map_subtype_le _).trans inf_le_left
    have hPp : IsPGroup 2 P :=
      (pCore_isPGroup (p := 2) (G := ↥(H z ⊓ G₀))).map (H z ⊓ G₀).subtype
    have hPn : (P.subgroupOf (H z)).Normal := by
      refine ⟨fun p hp g => ?_⟩
      have hp' : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hp
      have h1 := CFSG.Quasithin.SteinbergCD.mem_normalizer_inSubgroup_pCore 2 (hnorm g g.2)
      exact Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp h1 p).mp hp')
    have hPle : P.subgroupOf (H z) ≤ pCore 2 (H z) :=
      le_sSup ⟨hPn, hPp.comap_subtype⟩
    have hx' : (⟨x, hPH hx⟩ : ↥(H z)) ∈ P.subgroupOf (H z) := Subgroup.mem_subgroupOf.mpr hx
    exact ⟨_, hPle hx', rfl⟩
  · intro x hx
    let N : Subgroup ↥(H z ⊓ G₀) := (J z ⊓ G₀).subgroupOf (H z ⊓ G₀)
    have hNn : N.Normal := by
      refine ⟨fun y hy g => ?_⟩
      have hy' := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)
      refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
      · exact (Subgroup.mem_normalizer_iff.mp (hJN g.2.1) y).mp hy'.1
      · exact hG₀.conj_mem _ hy'.2 _
    have hNp : IsPGroup 2 N := (hJp.to_inf_left (K := G₀)).comap_subtype
    have hNle : N ≤ pCore 2 ↥(H z ⊓ G₀) := le_sSup ⟨hNn, hNp⟩
    have hx' : (⟨x, Subgroup.mem_inf.mpr ⟨J_le_H hx.1, hx.2⟩⟩ : ↥(H z ⊓ G₀)) ∈ N :=
      Subgroup.mem_subgroupOf.mpr hx
    exact ⟨_, hNle hx', rfl⟩

section IndexTwo

variable {z₁ : G} {G₀ : Subgroup G}

omit [Finite G] in
theorem J_decomp (hG₀i : G₀.index = 2) (hz₁G₀ : z₁ ∉ G₀) (hz₁ : z₁ ∈ J z)
    (hz₁2 : z₁ * z₁ = 1) {a : G} (ha : a ∈ J z) :
    ∃ a₀ ∈ J z ⊓ G₀, ∃ c ∈ Subgroup.zpowers z₁, a = a₀ * c := by
  by_cases haG₀ : a ∈ G₀
  · exact ⟨a, Subgroup.mem_inf.mpr ⟨ha, haG₀⟩, 1, Subgroup.one_mem _, by simp⟩
  · have h1 : a * z₁ ∈ G₀ :=
      (Subgroup.mul_mem_iff_of_index_two hG₀i).mpr (iff_of_false haG₀ hz₁G₀)
    refine ⟨a * z₁, Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ ha hz₁, h1⟩, z₁,
      Subgroup.mem_zpowers z₁, ?_⟩
    calc a = a * (z₁ * z₁) := by rw [hz₁2, mul_one]
      _ = a * z₁ * z₁ := by rw [mul_assoc]

omit [Finite G] in
theorem commute_zpowers_of_mem_centerIn (hz₁ : z₁ ∈ centerIn (J z)) {c : G}
    (hc : c ∈ Subgroup.zpowers z₁) {x : G} (hx : x ∈ J z) : x * c = c * x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  exact (Commute.zpow_right (Subgroup.mem_centralizer_iff.mp hz₁.2 x hx) k).eq

theorem card_J_inf (h : Tim79a.ParrottHyp z) (hz₁ : z₁ ∈ J z) (hG₀i : G₀.index = 2)
    (hz₁G₀ : z₁ ∉ G₀) : Nat.card ↥(J z ⊓ G₀) = 2 ^ 9 := by
  have h1 := Subgroup.relIndex_mul_card G₀ (J z)
  have h2 : G₀.relIndex (J z) = 2 := by
    have h3 : G₀.relIndex (J z) ≤ G₀.relIndex ⊤ :=
      Subgroup.relIndex_le_of_le_right le_top (by rw [Subgroup.relIndex_top_right, hG₀i]; omega)
    rw [Subgroup.relIndex_top_right, hG₀i] at h3
    have h4 : G₀.relIndex (J z) ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      exact fun hle => hz₁G₀ (hle hz₁)
    have h5 : G₀.relIndex (J z) ≠ 0 := by
      intro h0
      rw [h0] at h1
      have : 0 < Nat.card (J z) := Nat.card_pos
      omega
    omega
  rw [h2, card_J h, inf_comm] at h1
  omega

theorem commutator_J_inf (h : Tim79a.ParrottHyp z) (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁2 : orderOf z₁ = 2) (hG₀i : G₀.index = 2) (hz₁G₀ : z₁ ∉ G₀) :
    ⁅J z ⊓ G₀, J z ⊓ G₀⁆ = Subgroup.zpowers z := by
  have hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z := h.2.2.1
  have hz₁z₁ : z₁ * z₁ = 1 := by
    have h1 := pow_orderOf_eq_one z₁
    rwa [hz₁2, pow_two] at h1
  have hle : ⁅J z ⊓ G₀, J z ⊓ G₀⁆ ≤ Subgroup.zpowers z := by
    rw [← hcomm]
    exact Subgroup.commutator_mono inf_le_left inf_le_left
  have hcard : Nat.card ↥(⁅J z ⊓ G₀, J z ⊓ G₀⁆) ∣ 2 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, h.1] at this
  rcases (Nat.dvd_prime Nat.prime_two).mp hcard with h1 | h2
  · exfalso
    have hbot : ⁅J z ⊓ G₀, J z ⊓ G₀⁆ = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    have hJ₀ : ∀ a ∈ J z ⊓ G₀, ∀ b ∈ J z ⊓ G₀, a * b = b * a := by
      intro a ha b hb
      have h3 := Subgroup.commutator_mem_commutator ha hb
      rw [hbot, Subgroup.mem_bot, commutatorElement_def] at h3
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [h3, one_mul]
    have hJ : ∀ a ∈ J z, ∀ b ∈ J z, a * b = b * a := by
      intro a ha b hb
      obtain ⟨a₀, ha₀, c, hc, rfl⟩ := J_decomp hG₀i hz₁G₀ hz₁.1 hz₁z₁ ha
      obtain ⟨b₀, hb₀, d, hd, rfl⟩ := J_decomp hG₀i hz₁G₀ hz₁.1 hz₁z₁ hb
      have hcd : c * d = d * c := by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
        exact ((Commute.refl z₁).zpow_zpow i k).eq
      have hcb := commute_zpowers_of_mem_centerIn hz₁ hc (Subgroup.mem_inf.mp hb₀).1
      have hda := commute_zpowers_of_mem_centerIn hz₁ hd (Subgroup.mem_inf.mp ha₀).1
      calc a₀ * c * (b₀ * d) = a₀ * (c * b₀) * d := by group
        _ = a₀ * (b₀ * c) * d := by rw [← hcb]
        _ = a₀ * b₀ * (c * d) := by group
        _ = b₀ * a₀ * (d * c) := by rw [hJ₀ a₀ ha₀ b₀ hb₀, hcd]
        _ = b₀ * (a₀ * d) * c := by group
        _ = b₀ * (d * a₀) * c := by rw [← hda]
        _ = b₀ * d * (a₀ * c) := by group
    have hJbot : ⁅J z, J z⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hJ a ha b hb).symm
    rw [hcomm, Subgroup.zpowers_eq_bot] at hJbot
    have hz2 : orderOf z = 2 := h.1
    rw [hJbot, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  · exact le_antisymm hle (by
      have := Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, h.1, h2])
      rw [this])

omit [Finite G] in
theorem mem_centralizer_J_of_mem_centralizer_J_inf (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁2 : orderOf z₁ = 2) (hG₀i : G₀.index = 2) (hz₁G₀ : z₁ ∉ G₀) {x : G}
    (hx : x ∈ Subgroup.centralizer ((J z ⊓ G₀ : Subgroup G) : Set G))
    (hxz₁ : x * z₁ = z₁ * x) : x ∈ Subgroup.centralizer (J z : Set G) := by
  have hz₁z₁ : z₁ * z₁ = 1 := by
    have h1 := pow_orderOf_eq_one z₁
    rwa [hz₁2, pow_two] at h1
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨a₀, ha₀, c, hc, rfl⟩ := J_decomp hG₀i hz₁G₀ hz₁.1 hz₁z₁ ha
  have hxc : x * c = c * x := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact (Commute.zpow_right (show Commute x z₁ from hxz₁) k).eq
  have hxa : a₀ * x = x * a₀ := Subgroup.mem_centralizer_iff.mp hx a₀ ha₀
  calc a₀ * c * x = a₀ * (c * x) := by rw [mul_assoc]
    _ = a₀ * (x * c) := by rw [← hxc]
    _ = a₀ * x * c := by rw [mul_assoc]
    _ = x * a₀ * c := by rw [hxa]
    _ = x * (a₀ * c) := by rw [mul_assoc]

theorem centerIn_J_inf (h : Tim79a.ParrottHyp z) (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2) (hG₀i : G₀.index = 2)
    (hzG₀ : z ∈ G₀) (hz₁G₀ : z₁ ∉ G₀) : centerIn (J z ⊓ G₀) = Subgroup.zpowers z := by
  apply le_antisymm
  · rintro x ⟨hxJ, hxC⟩
    have hxz₁ : x * z₁ = z₁ * x :=
      Subgroup.mem_centralizer_iff.mp hz₁.2 x (Subgroup.mem_inf.mp hxJ).1
    have hxA : x ∈ centerIn (J z) :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hxJ).1,
        mem_centralizer_J_of_mem_centralizer_J_inf hz₁ hz₁2 hG₀i hz₁G₀ hxC hxz₁⟩
    have hxG₀ : x ∈ G₀ := (Subgroup.mem_inf.mp hxJ).2
    rcases (mem_centerIn_J_iff h hz₁ hz₁z hz₁2).mp hxA with h1 | h1 | h1 | h1
    · rw [h1]
      exact Subgroup.one_mem _
    · rw [h1]
      exact Subgroup.mem_zpowers z
    · exact absurd (h1 ▸ hxG₀) hz₁G₀
    · exfalso
      apply hz₁G₀
      have h2 : z⁻¹ * (z * z₁) ∈ G₀ := G₀.mul_mem (G₀.inv_mem hzG₀) (h1 ▸ hxG₀)
      rwa [inv_mul_cancel_left] at h2
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨z_mem_J h, hzG₀⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_iff.mp (z_mem_centerIn_J h).2 a (Subgroup.mem_inf.mp ha).1

theorem isExtraspecial2_J_inf (h : Tim79a.ParrottHyp z) (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2) (hG₀i : G₀.index = 2)
    (hzG₀ : z ∈ G₀) (hz₁G₀ : z₁ ∉ G₀) : IsExtraspecial2 (J z ⊓ G₀) := by
  refine ⟨(isPGroup_J h).to_inf_left, ?_, ?_⟩
  · rw [← CFSG.centerIn_eq_map_center, centerIn_J_inf h hz₁ hz₁z hz₁2 hG₀i hzG₀ hz₁G₀,
      commutator_J_inf h hz₁ hz₁2 hG₀i hz₁G₀]
  · rw [commutator_J_inf h hz₁ hz₁2 hG₀i hz₁G₀, Nat.card_zpowers, h.1]

omit [Finite G] in
theorem centralizer_inf_le_J_inf (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁2 : orderOf z₁ = 2) (hG₀i : G₀.index = 2)
    (hz₁G₀ : z₁ ∉ G₀) :
    H z ⊓ G₀ ⊓ Subgroup.centralizer ((J z ⊓ G₀ : Subgroup G) : Set G) ≤ J z ⊓ G₀ := by
  intro x hx
  obtain ⟨⟨hxH, hxG₀⟩, hxC⟩ := hx
  have hz₁' : z₁ ∈ centerIn (H z) := hZ ▸ hz₁
  have hxz₁ : x * z₁ = z₁ * x := Subgroup.mem_centralizer_iff.mp hz₁'.2 x hxH
  have hxJ : x ∈ Subgroup.centralizer (J z : Set G) :=
    mem_centralizer_J_of_mem_centralizer_J_inf hz₁ hz₁2 hG₀i hz₁G₀ hxC hxz₁
  exact Subgroup.mem_inf.mpr ⟨h.2.2.2.1 (Subgroup.mem_inf.mpr ⟨hxH, hxJ⟩), hxG₀⟩

end IndexTwo

end CFSG.RankThree.GF2n.Parrott

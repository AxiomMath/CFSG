module

public import CFSG.OddTranspositions.SevenThreeKind
public import CFSG.OddTranspositions.SixSevenLocalStep

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem conj_Aalpha_eq_of_order_three (hC : HypothesisC D)
    (h3 : ∀ x ∈ D, ∀ g : ConjAct G, x ∈ g • hC.alpha →
      ∀ y ∈ AalphaStar D (g • hC.alpha), orderOf (x * y) = 3)
    {v : G} (hv : v ∈ hC.alpha) {β : Set G} (hβ : β ∈ Aalpha D hC.alpha) :
    (fun x => hC.d * x * hC.d⁻¹) '' β = (fun x => v * x * v⁻¹) '' β := by
  classical
  have hdD : hC.d ∈ D := hC.isBlock_alpha.subset hC.d_mem_alpha
  have hvD : v ∈ D := hC.isBlock_alpha.subset hv
  have hd2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hdD
  have hv2 : v * v = 1 := hC.setup.oddT.mul_self_eq_one hvD
  have key : ∀ b ∈ β, (fun x => hC.d * x * hC.d⁻¹) '' β =
      (fun x => b * x * b⁻¹) '' hC.alpha := by
    intro b hb
    have hbA : b ∈ AalphaStar D hC.alpha := ⟨β, hβ, hb⟩
    have hbD : b ∈ D := AalphaStar_subset hC.setup.normal hC.isBlock_alpha hbA
    have hb2 : b * b = 1 := hC.setup.oddT.mul_self_eq_one hbD
    have h3d : orderOf (hC.d * b) = 3 :=
      h3 hC.d hdD 1 (by simpa using hC.d_mem_alpha) b (by simpa using hbA)
    have h3v : orderOf (v * b) = 3 :=
      h3 v hvD 1 (by simpa using hv) b (by simpa using hbA)
    have hd_eq : hC.d * b * hC.d = b * hC.d * b := by
      have h := conj_eq_of_orderOf_mul_eq_three hb2 hd2 (by rwa [orderOf_mul_comm_eq] at h3d)
      exact h
    have hv_eq : v * b * v = b * v * b := by
      have h := conj_eq_of_orderOf_mul_eq_three hb2 hv2 (by rwa [orderOf_mul_comm_eq] at h3v)
      exact h
    have hmem : (hC.d * b * hC.d) ∈
        ((fun x => hC.d * x * hC.d⁻¹) '' β) ∩ ((fun x => b * x * b⁻¹) '' hC.alpha) := by
      constructor
      · exact ⟨b, hb, by rw [inv_eq_of_mul_eq_one_right hd2]⟩
      · exact ⟨hC.d, hC.d_mem_alpha, by
          rw [inv_eq_of_mul_eq_one_right hb2]
          exact hd_eq.symm⟩
    have hαmem : hC.alpha ∈ blockClass hC.alpha := mem_blockClass_iff'.mpr ⟨1, by simp⟩
    exact eq_of_mem_of_mem_blockClass hC.isBlock_alpha
      (conj_image_mem_blockClass hβ.1 hC.d) (conj_image_mem_blockClass hαmem b) ⟨_, hmem⟩
  obtain ⟨b, hb⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hβ.1
  have hbD : b ∈ D := AalphaStar_subset hC.setup.normal hC.isBlock_alpha ⟨β, hβ, hb⟩
  have hb2 : b * b = 1 := hC.setup.oddT.mul_self_eq_one hbD
  have hbA : b ∈ AalphaStar D hC.alpha := ⟨β, hβ, hb⟩
  have h3d : orderOf (hC.d * b) = 3 :=
    h3 hC.d hdD 1 (by simpa using hC.d_mem_alpha) b (by simpa using hbA)
  have h3v : orderOf (v * b) = 3 :=
    h3 v hvD 1 (by simpa using hv) b (by simpa using hbA)
  have hv_eq : v * b * v = b * v * b :=
    conj_eq_of_orderOf_mul_eq_three hb2 hv2 (by rwa [orderOf_mul_comm_eq] at h3v)
  have hmem : (v * b * v) ∈
      ((fun x => v * x * v⁻¹) '' β) ∩ ((fun x => b * x * b⁻¹) '' hC.alpha) := by
    constructor
    · exact ⟨b, hb, by rw [inv_eq_of_mul_eq_one_right hv2]⟩
    · exact ⟨v, hv, by rw [inv_eq_of_mul_eq_one_right hb2]; exact hv_eq.symm⟩
  have hαmem : hC.alpha ∈ blockClass hC.alpha := mem_blockClass_iff'.mpr ⟨1, by simp⟩
  have hvb : (fun x => v * x * v⁻¹) '' β = (fun x => b * x * b⁻¹) '' hC.alpha :=
    eq_of_mem_of_mem_blockClass hC.isBlock_alpha
      (conj_image_mem_blockClass hβ.1 v) (conj_image_mem_blockClass hαmem b) ⟨_, hmem⟩
  rw [key b hb, hvb]

theorem actsTrivially_mul_of_order_three (hC : HypothesisC D)
    (h3 : ∀ x ∈ D, ∀ g : ConjAct G, x ∈ g • hC.alpha →
      ∀ y ∈ AalphaStar D (g • hC.alpha), orderOf (x * y) = 3)
    {v : G} (hv : v ∈ hC.alpha) :
    ActsTriviallyOnBlocks hC.alpha (hC.d * v) := by
  intro β hβ
  rw [← perp_union_Aalpha_eq_blockClass] at hβ
  rcases hβ with hβp | hβA
  · rcases mem_perp_iff.mp hβp with hβD | hβα
    ·
      obtain ⟨-, -, -, hcomm⟩ := mem_Dalpha_iff.mp hβD
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        change (hC.d * v) * z * (hC.d * v)⁻¹ ∈ β
        have hdz : Commute hC.d z := hcomm hC.d hC.d_mem_alpha z hz
        have hvz : Commute v z := hcomm v hv z hz
        have hcommdv : Commute (hC.d * v) z := hdz.mul_left hvz
        rw [hcommdv.eq, mul_assoc, mul_inv_cancel, mul_one]
        exact hz
      · intro hy
        refine ⟨y, hy, ?_⟩
        change (hC.d * v) * y * (hC.d * v)⁻¹ = y
        have hdy : Commute hC.d y := hcomm hC.d hC.d_mem_alpha y hy
        have hvy : Commute v y := hcomm v hv y hy
        have hcommdv : Commute (hC.d * v) y := hdy.mul_left hvy
        rw [hcommdv.eq, mul_assoc, mul_inv_cancel, mul_one]
    ·
      subst hβα
      have hdN : hC.d ∈ Subgroup.normalizer hC.alpha :=
        mem_normalizer_of_mem_alpha hC.isBlock_alpha hC.d_mem_alpha
      have hvN : v ∈ Subgroup.normalizer hC.alpha :=
        mem_normalizer_of_mem_alpha hC.isBlock_alpha hv
      have hdvN : hC.d * v ∈ Subgroup.normalizer hC.alpha := Subgroup.mul_mem _ hdN hvN
      exact Subgroup.mem_normalizer_iff_conj_image_eq.mp hdvN
  ·
    have h51 := conj_Aalpha_eq_of_order_three hC h3 hv hβA
    have hd2 : hC.d * hC.d = 1 :=
      hC.setup.oddT.mul_self_eq_one (hC.isBlock_alpha.subset hC.d_mem_alpha)
    calc (fun y => (hC.d * v) * y * (hC.d * v)⁻¹) '' β
        = (fun y => hC.d * y * hC.d⁻¹) '' ((fun y => v * y * v⁻¹) '' β) := by
          rw [Set.image_image]
          congr 1
          funext z
          group
      _ = (fun y => hC.d * y * hC.d⁻¹) '' ((fun y => hC.d * y * hC.d⁻¹) '' β) := by
          rw [h51]
      _ = β := by
          rw [Set.image_image]
          have hfun : (fun y => hC.d * (hC.d * y * hC.d⁻¹) * hC.d⁻¹) = id := by
            funext z
            rw [show hC.d * (hC.d * z * hC.d⁻¹) * hC.d⁻¹ = z by
              have hdinv : hC.d⁻¹ = hC.d := inv_eq_of_mul_eq_one_right hd2
              rw [hdinv]
              calc hC.d * (hC.d * z * hC.d) * hC.d
                  = (hC.d * hC.d) * z * (hC.d * hC.d) := by group
                _ = z := by rw [hd2, one_mul, mul_one]]
            rfl
          rw [hfun, Set.image_id]

theorem sevenThree_of_faithful_of_ne (hC : HypothesisC D)
    (h3 : ∀ x ∈ D, ∀ g : ConjAct G, x ∈ g • hC.alpha →
      ∀ y ∈ AalphaStar D (g • hC.alpha), orderOf (x * y) = 3)
    (hfaith : FaithfulOnBlocks hC.alpha) {v : G} (hv : v ∈ hC.alpha) (hvd : v ≠ hC.d) :
    ∃ w ∈ AalphaStar D hC.alpha, orderOf (hC.d * w) ≠ 3 := by
  by_contra h
  push Not at h
  have htriv : ActsTriviallyOnBlocks hC.alpha (hC.d * v) :=
    actsTrivially_mul_of_order_three hC h3 hv
  have h1 : hC.d * v = 1 := hfaith _ htriv
  have hd2 : hC.d * hC.d = 1 :=
    hC.setup.oddT.mul_self_eq_one (hC.isBlock_alpha.subset hC.d_mem_alpha)
  have hv_eq : v = hC.d := by
    have h2 : v = hC.d⁻¹ := eq_inv_of_mul_eq_one_right h1
    rwa [inv_eq_of_mul_eq_one_right hd2] at h2
  exact hvd hv_eq

theorem exists_mem_alpha_ne_of_not_threeTranspositions (hC : HypothesisC D)
    (h3 : ∀ w ∈ AalphaStar D hC.alpha, orderOf (hC.d * w) = 3)
    (hnot3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) :
    ∃ v ∈ hC.alpha, v ≠ hC.d := by
  by_contra h
  push Not at h
  have hα : hC.alpha = {hC.d} := by
    ext v
    constructor
    · intro hv
      exact Set.mem_singleton_iff.mpr (h v hv)
    · intro hv
      rw [Set.mem_singleton_iff] at hv
      rw [hv]
      exact hC.d_mem_alpha
  apply hnot3
  intro x hxD y hyD
  have hx2 : x * x = 1 := hC.setup.oddT.mul_self_eq_one hxD
  have hy2 : y * y = 1 := hC.setup.oddT.mul_self_eq_one hyD
  by_cases hxy : Commute x y
  · have hsq : (x * y) * (x * y) = 1 := by
      calc (x * y) * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [← hxy.eq]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hx2, hy2, mul_one]
    have hdvd : orderOf (x * y) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hsq)
    have hpos : 0 < orderOf (x * y) := orderOf_pos _
    have hle : orderOf (x * y) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases orderOf (x * y) <;> simp
  · have hodd : Odd (orderOf (x * y)) := hC.setup.oddT.odd_of_not_commute hxD hyD hxy
    obtain ⟨g, hg⟩ := isConj_iff.mp
      (isConj_of_isClass hC.setup.isClass hxD (hC.isBlock_alpha.subset hC.d_mem_alpha))
    let y' : G := g * y * g⁻¹
    have hy'D : y' ∈ D := hC.setup.normal g y hyD
    have hdy' : ¬ Commute hC.d y' := by
      intro hc
      apply hxy
      have h := hc.conj g⁻¹
      simp only [inv_inv] at h
      have e1 : g⁻¹ * hC.d * g = x := by rw [← hg]; group
      have e2 : g⁻¹ * y' * g = y := by simp [y']; group
      rw [e1, e2] at h
      exact h
    have hy'α : y' ∉ hC.alpha := by
      rw [hα]
      simp only [Set.mem_singleton_iff]
      intro h
      apply hdy'
      rw [h]
    have hy'A : y' ∈ AalphaStar D hC.alpha := by
      rw [hC.AalphaStar_eq_diff_alpha]
      exact ⟨⟨hy'D, fun hc => hdy' hc.symm⟩, hy'α⟩
    have hxy_eq : orderOf (x * y) = orderOf (hC.d * y') := by
      have e1 : x = g⁻¹ * hC.d * g := by rw [← hg]; group
      have e2 : y = g⁻¹ * y' * g := by simp [y']; group
      have e : x * y = g⁻¹ * (hC.d * y') * g := by rw [e1, e2]; group
      calc orderOf (x * y) = orderOf (g⁻¹ * (hC.d * y') * g) := by rw [e]
        _ = orderOf (hC.d * y') := by
          simpa using orderOf_conj_eq (g⁻¹) (hC.d * y')
    rw [hxy_eq, h3 y' hy'A]
    simp

theorem sevenThree_of_faithful (hC : HypothesisC D)
    (h3 : ∀ x ∈ D, ∀ g : ConjAct G, x ∈ g • hC.alpha →
      ∀ y ∈ AalphaStar D (g • hC.alpha), orderOf (x * y) = 3)
    (hfaith : FaithfulOnBlocks hC.alpha)
    (hnot3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) :
    ∃ w ∈ AalphaStar D hC.alpha, orderOf (hC.d * w) ≠ 3 := by
  by_contra h
  push Not at h
  obtain ⟨v, hv, hvd⟩ := exists_mem_alpha_ne_of_not_threeTranspositions hC h hnot3
  obtain ⟨w, hw, hw3⟩ := sevenThree_of_faithful_of_ne hC h3 hfaith hv hvd
  exact hw3 (h w hw)

end CFSG.OddTranspositions





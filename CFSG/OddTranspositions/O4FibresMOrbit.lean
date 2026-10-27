module

public import CFSG.OddTranspositions.HalphaLocalSecond
public import CFSG.OddTranspositions.ConfigWidth

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ CFSG.GroupTheory

variable {G : Type} [Group G] [Finite G] {D : Set G} {u w v z a : G} {K₁ S' : Subgroup G}

theorem conj_pow_eq_of_odd_mul {G : Type} [Group G] {d e : G} (hd : d * d = 1)
    (he : e * e = 1) (hodd : Odd (orderOf (d * e))) :
    (d * e) ^ ((orderOf (d * e) - 1) / 2) * d *
        ((d * e) ^ ((orderOf (d * e) - 1) / 2))⁻¹ = e := by
  obtain ⟨k, hk⟩ := hodd
  have hk' : (orderOf (d * e) - 1) / 2 = k := by omega
  rw [hk']
  exact conj_eq_of_odd hd he hk

theorem exists_mem_conj_of_odd (hC : HypothesisC D) {d d' : DstarH hC}
    (hmk : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (d : Halpha D hC.alpha) =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (d' : Halpha D hC.alpha))
    (hodd : Odd (orderOf ((d : Halpha D hC.alpha) * (d' : Halpha D hC.alpha)))) :
    ∃ m : Halpha D hC.alpha,
      m ∈ CFSG.solvableRadical (Halpha D hC.alpha) ∧ m * d * m⁻¹ = d' := by
  classical
  obtain ⟨k, hk⟩ := hodd
  have hd2 : (d : Halpha D hC.alpha) * (d : Halpha D hC.alpha) = 1 :=
    (DstarH_isOddTransp hC).mul_self_eq_one d.2
  have hd'2 : (d' : Halpha D hC.alpha) * (d' : Halpha D hC.alpha) = 1 :=
    (DstarH_isOddTransp hC).mul_self_eq_one d'.2
  have hxM : (d : Halpha D hC.alpha) * (d' : Halpha D hC.alpha) ∈
      CFSG.solvableRadical (Halpha D hC.alpha) := by
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
      ((d : Halpha D hC.alpha) * (d' : Halpha D hC.alpha)) = 1
    rw [map_mul, ← hmk, ← map_mul, hd2, map_one]
  refine ⟨((d : Halpha D hC.alpha) * (d' : Halpha D hC.alpha)) ^ k,
    Subgroup.pow_mem (K := CFSG.solvableRadical (Halpha D hC.alpha)) hxM k, ?_⟩
  have hk' : (orderOf ((d : Halpha D hC.alpha) * (d' : Halpha D hC.alpha)) - 1) / 2 = k := by
    omega
  have h := conj_pow_eq_of_odd_mul hd2 hd'2 ⟨k, hk⟩
  rwa [hk'] at h

theorem mk_eq_of_mem_conj (hC : HypothesisC D) {d d' : DstarH hC}
    {m : Halpha D hC.alpha} (hm : m ∈ CFSG.solvableRadical (Halpha D hC.alpha))
    (hmconj : m * d * m⁻¹ = d') :
    QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (d : Halpha D hC.alpha) =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (d' : Halpha D hC.alpha) := by
  have hm1 : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) m = 1 :=
    (QuotientGroup.eq_one_iff m).mpr hm
  rw [← hmconj, map_mul, map_mul, map_inv, hm1, one_mul, inv_one, mul_one]

theorem exists_transpositions_commute_ne {τ : Equiv.Perm (Fin 5)} (hτ : τ ∈ transpositions) :
    ∃ τ₂ ∈ transpositions, τ₂ ≠ τ ∧ Commute τ τ₂ := by
  have hcard := card_transpositions_commuting τ hτ
  have hpos : 0 < Nat.card {σ : Equiv.Perm (Fin 5) // σ.IsSwap ∧ σ ≠ τ ∧ Commute σ τ} := by
    rw [hcard]
    norm_num
  obtain ⟨⟨σ, hσ, hne, hcomm⟩⟩ := Nat.card_pos_iff.mp hpos
  exact ⟨σ, hσ, hne, hcomm.symm⟩

theorem exists_lift_eq_symm (hC : HypothesisC D)
    {e : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
      Equiv.Perm (Fin 5)}
    (hIm : e '' imageClass hC = transpositions)
    {τ : Equiv.Perm (Fin 5)} (hτ : τ ∈ transpositions) :
    ∃ d : DstarH hC,
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (d : Halpha D hC.alpha) = e.symm τ := by
  have hτim : τ ∈ e '' imageClass hC := by rw [hIm]; exact hτ
  obtain ⟨q, hq, hqe⟩ := hτim
  have hqeq : q = e.symm τ := by
    rw [← hqe, MulEquiv.symm_apply_apply]
  obtain ⟨d, hd, hdmk⟩ := hq
  exact ⟨⟨d, hd⟩, hdmk.trans hqeq⟩

theorem not_commute_of_mk_eq (hC : HypothesisC D) (hQ : Config D u w v z a K₁ S')
    {e : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
      Equiv.Perm (Fin 5)}
    (hIm : e '' imageClass hC = transpositions)
    {d d' : DstarH hC}
    (hmk : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (d : Halpha D hC.alpha) =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (d' : Halpha D hC.alpha)) (hne : d ≠ d') :
    ¬ Commute (d : Halpha D hC.alpha) (d' : Halpha D hC.alpha) := by
  classical
  intro hcomm
  have hd_img_mem : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
      (d : Halpha D hC.alpha) ∈ imageClass hC := ⟨d, d.2, rfl⟩
  have hτ' : e (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
      (d : Halpha D hC.alpha)) ∈ transpositions := by
    have h : e (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (d : Halpha D hC.alpha)) ∈ e '' imageClass hC := ⟨_, hd_img_mem, rfl⟩
    rwa [hIm] at h
  obtain ⟨τ₂, hτ₂, hτ₂ne, hτ₂comm⟩ := exists_transpositions_commute_ne hτ'
  obtain ⟨d₂, hd₂⟩ := exists_lift_eq_symm hC hIm hτ₂
  have hne_d_d₂ : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
      (d : Halpha D hC.alpha) ≠
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (d₂ : Halpha D hC.alpha) := by
    intro h
    apply hτ₂ne
    have h' := congrArg e h
    rw [hd₂] at h'
    simpa using h'.symm
  have hne_d'_d₂ : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
      (d' : Halpha D hC.alpha) ≠
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (d₂ : Halpha D hC.alpha) := by
    rw [← hmk]
    exact hne_d_d₂
  have hcomm_d_d₂ : Commute (d : Halpha D hC.alpha) (d₂ : Halpha D hC.alpha) := by
    apply commute_of_commute_mk_of_ne_H hC d.2 d₂.2
    · have h : Commute (e (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
          (d : Halpha D hC.alpha)))
          (e (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
            (d₂ : Halpha D hC.alpha))) := by
        rw [hd₂]
        simpa using hτ₂comm
      simpa using h.map e.symm
    · exact hne_d_d₂
  have hcomm_d'_d₂ : Commute (d' : Halpha D hC.alpha) (d₂ : Halpha D hC.alpha) := by
    apply commute_of_commute_mk_of_ne_H hC d'.2 d₂.2
    · have h : Commute (e (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
          (d' : Halpha D hC.alpha)))
          (e (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
            (d₂ : Halpha D hC.alpha))) := by
        rw [← hmk, hd₂]
        simpa using hτ₂comm
      simpa using h.map e.symm
    · exact hne_d'_d₂
  have hc_not_Dstar : hC.d ∉ DalphaStar D hC.alpha := by
    intro hmem
    have hdE : hC.d ∈ hC.E := by rwa [hC.DalphaStar_alpha] at hmem
    have hdα : hC.d ∈ hC.alpha := hC.d_mem_alpha
    rw [hC.alpha_eq_normSet_diff] at hdα
    exact hdα.2 hdE
  have hc_ne_d : hC.d ≠ ((d : Halpha D hC.alpha) : G) := by
    intro h
    exact hc_not_Dstar (h ▸ (mem_DstarH_iff hC).mp d.2)
  have hc_ne_d' : hC.d ≠ ((d' : Halpha D hC.alpha) : G) := by
    intro h
    exact hc_not_Dstar (h ▸ (mem_DstarH_iff hC).mp d'.2)
  have hc_ne_d₂ : hC.d ≠ ((d₂ : Halpha D hC.alpha) : G) := by
    intro h
    exact hc_not_Dstar (h ▸ (mem_DstarH_iff hC).mp d₂.2)
  have hdd' : ((d : Halpha D hC.alpha) : G) ≠ ((d' : Halpha D hC.alpha) : G) := by
    intro h
    exact hne (Subtype.ext (Subtype.ext h))
  have hdd₂ : ((d : Halpha D hC.alpha) : G) ≠ ((d₂ : Halpha D hC.alpha) : G) := by
    intro h
    exact hne_d_d₂ (congrArg (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))
      (Subtype.ext h))
  have hd'd₂ : ((d' : Halpha D hC.alpha) : G) ≠ ((d₂ : Halpha D hC.alpha) : G) := by
    intro h
    exact hne_d'_d₂ (congrArg (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))
      (Subtype.ext h))
  let S : Finset G := {hC.d, ((d : Halpha D hC.alpha) : G),
    ((d' : Halpha D hC.alpha) : G), ((d₂ : Halpha D hC.alpha) : G)}
  have hS_card : S.card = 4 := by
    simp [S, hc_ne_d, hc_ne_d', hc_ne_d₂, hdd', hdd₂, hd'd₂]
  have hSD : (↑S : Set G) ⊆ D := by
    intro x hx
    simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hC.isBlock_alpha.subset hC.d_mem_alpha
    · exact DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp d.2)
    · exact DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp d'.2)
    · exact DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp d₂.2)
  have hScomm : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Commute x y := by
    intro x hx y hy hxy
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx hy
    have hcd : Commute hC.d ((d : Halpha D hC.alpha) : G) :=
      (hC.DalphaStar_subset_commute ((mem_DstarH_iff hC).mp d.2)).2.symm
    have hcd' : Commute hC.d ((d' : Halpha D hC.alpha) : G) :=
      (hC.DalphaStar_subset_commute ((mem_DstarH_iff hC).mp d'.2)).2.symm
    have hcd₂ : Commute hC.d ((d₂ : Halpha D hC.alpha) : G) :=
      (hC.DalphaStar_subset_commute ((mem_DstarH_iff hC).mp d₂.2)).2.symm
    have hdd'c : Commute ((d : Halpha D hC.alpha) : G) ((d' : Halpha D hC.alpha) : G) :=
      hcomm.map (Halpha D hC.alpha).subtype
    have hdd₂c : Commute ((d : Halpha D hC.alpha) : G) ((d₂ : Halpha D hC.alpha) : G) :=
      hcomm_d_d₂.map (Halpha D hC.alpha).subtype
    have hd'd₂c : Commute ((d' : Halpha D hC.alpha) : G) ((d₂ : Halpha D hC.alpha) : G) :=
      hcomm_d'_d₂.map (Halpha D hC.alpha).subtype
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
    · exact absurd rfl hxy
    · exact hcd
    · exact hcd'
    · exact hcd₂
    · exact hcd.symm
    · exact absurd rfl hxy
    · exact hdd'c
    · exact hdd₂c
    · exact hcd'.symm
    · exact hdd'c.symm
    · exact absurd rfl hxy
    · exact hd'd₂c
    · exact hcd₂.symm
    · exact hdd₂c.symm
    · exact hd'd₂c.symm
    · exact absurd rfl hxy
  have hle : S.card ≤ 3 := widthLe_three_of_config hQ S hSD hScomm
  rw [hS_card] at hle
  omega

theorem mk_eq_m_conj_of_config (hC : HypothesisC D) (hQ : Config D u w v z a K₁ S')
    {e : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
      Equiv.Perm (Fin 5)}
    (hIm : e '' imageClass hC = transpositions) {d d' : DstarH hC}
    (hmk : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (d : Halpha D hC.alpha) =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (d' : Halpha D hC.alpha)) :
    ∃ m : Halpha D hC.alpha,
      m ∈ CFSG.solvableRadical (Halpha D hC.alpha) ∧ m * d * m⁻¹ = d' := by
  by_cases hdd : d = d'
  · subst hdd
    exact ⟨1, Subgroup.one_mem _, by simp⟩
  · have hnc := not_commute_of_mk_eq hC hQ hIm hmk hdd
    have hodd := (DstarH_isOddTransp hC).odd_of_not_commute d.2 d'.2 hnc
    exact exists_mem_conj_of_odd hC hmk hodd

theorem mk_eq_iff_m_conj_of_config (hC : HypothesisC D) (hQ : Config D u w v z a K₁ S')
    {e : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
      Equiv.Perm (Fin 5)}
    (hIm : e '' imageClass hC = transpositions) {d d' : DstarH hC} :
    QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (d : Halpha D hC.alpha) =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (d' : Halpha D hC.alpha) ↔
      ∃ m : Halpha D hC.alpha,
        m ∈ CFSG.solvableRadical (Halpha D hC.alpha) ∧ m * d * m⁻¹ = d' := by
  constructor
  · exact mk_eq_m_conj_of_config hC hQ hIm
  · rintro ⟨m, hm, hmconj⟩
    exact mk_eq_of_mem_conj hC hm hmconj

end CFSG.OddTranspositions

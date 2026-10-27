module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588A3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.N588A

open Subgroup CFSG.ABGLocalTools
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)

namespace Hyp

variable {G : Type} [Group G] [Finite G] {p : ℕ} {S Z : Subgroup G}

theorem exists_orderOf_eq_of_isComponent (h : Hyp G p S Z) (hcore : CFSG.pPrimeCore p G = ⊥)
    {J : Subgroup G} (hJ : CFSG.IsComponent J) : ∃ x ∈ S ⊓ J, orderOf x = p := by
  haveI := h.fact
  have hsyl := isSylowOf_inf_of_isSubnormal h.sylow hJ.2
  have hdvd : p ∣ Nat.card (S ⊓ J : Subgroup G) := by
    rw [hsyl.card_eq]
    exact dvd_pow_self p
      (Nat.pos_iff_ne_zero.mp (h.prime.factorization_pos_of_dvd Nat.card_pos.ne'
        (h.dvd_card_of_isComponent hcore hJ)))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx]⟩

theorem inf_eq_bot_of_not_le (h : Hyp G p S Z) {J : Subgroup G} (hZJ : ¬ Z ≤ J) : Z ⊓ J = ⊥ := by
  have hdvd : Nat.card (Z ⊓ J : Subgroup G) ∣ p := h.card ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime h.prime).mp hdvd with h1 | hp
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    apply hZJ
    have heq : Z ⊓ J = Z := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hp, h.card])
    exact heq ▸ inf_le_right

theorem concl_of_sup_ne_top (ih : IHBelow (Nat.card G)) (h : Hyp G p S Z)
    (hcore : CFSG.pPrimeCore p G = ⊥) {J : Subgroup G} (hJ : CFSG.IsComponent J)
    (hZJ : ¬ Z ≤ Subgroup.centralizer (J : Set G)) (hNJ : Z ≤ Subgroup.normalizer (J : Set G))
    (hY : Z ⊔ J ≠ ⊤) : CFSG.Open.pRank p (normalClosure (Z : Set G)) = 1 := by
  haveI := h.fact
  set Y : Subgroup G := Z ⊔ J with hYdef
  have hZY : Z ≤ Y := le_sup_left
  have hJY : J ≤ Y := le_sup_right
  set XY : Subgroup G :=
    (normalClosure ((Z.subgroupOf Y : Subgroup Y) : Set Y)).map Y.subtype with hXY
  have hrank : CFSG.Open.pRank p XY = 1 := h.pRank_normalClosure_subgroup ih hZY hY
  have hZXY : Z ≤ XY := fun z hz =>
    ⟨⟨z, hZY hz⟩, Subgroup.le_normalClosure (Subgroup.mem_subgroupOf.mpr hz), rfl⟩
  have hJXY : J ≤ XY := by
    rcases CFSG.LocalCores.component_normal_subgroup (CFSG.LocalCores.component_overgroup hJ hJY)
        (Subgroup.normalClosure_normal (s := ((Z.subgroupOf Y : Subgroup Y) : Set Y))) with
      hle | hcomm
    · intro j hj
      exact ⟨⟨j, hJY hj⟩, hle (Subgroup.mem_subgroupOf.mpr hj), rfl⟩
    · exfalso
      apply hZJ
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have hc := Subgroup.mem_centralizer_iff.mp
        ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
          (Subgroup.mem_subgroupOf.mpr hj : (⟨j, hJY hj⟩ : Y) ∈ J.subgroupOf Y))
        ⟨z, hZY hz⟩ (Subgroup.le_normalClosure (Subgroup.mem_subgroupOf.mpr hz))
      exact (congrArg Subtype.val hc).symm
  have hZleJ : Z ≤ J := by
    by_contra hZJ'
    have hZJbot := h.inf_eq_bot_of_not_le hZJ'
    obtain ⟨x, hx, hxo⟩ := h.exists_orderOf_eq_of_isComponent hcore hJ
    have hB : Nat.card (zpowers x) = p := by rw [Nat.card_zpowers, hxo]
    have hBJ : zpowers x ≤ J := (Subgroup.zpowers_le).mpr hx.2
    have hBS : zpowers x ≤ S := (Subgroup.zpowers_le).mpr hx.1
    have h2 := two_le_pRank h.prime h.card hB (fun z hz b hb => h.comm hz (hBS hb))
      (le_bot_iff.mp (hZJbot ▸ inf_le_inf_left Z hBJ)) hZXY (hBJ.trans hJXY)
    omega
  have hJn : J.Normal := by
    have hconj : ∀ g : G, J.map (MulAut.conj g).toMonoidHom = J := by
      intro g
      by_contra hne
      have hJ' := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hJ
      have hcomm : ⁅J, J.map (MulAut.conj g).toMonoidHom⁆ = ⊥ :=
        (CFSG.LocalCores.distinct_components_commute hJ hJ').resolve_left (Ne.symm hne)
      have hJ'C : J.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer (J : Set G) := by
        rw [Subgroup.le_centralizer_iff]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      have hZgJ' : CFSG.conjugate Z g⁻¹ ≤ J.map (MulAut.conj g).toMonoidHom := by
        intro x hx
        rw [mem_conjugate_iff, inv_inv] at hx
        refine ⟨g⁻¹ * x * g, hZleJ hx, ?_⟩
        change g * (g⁻¹ * x * g) * g⁻¹ = x
        group
      have hZg : CFSG.conjugate Z g⁻¹ = Z := by
        apply h.conjugate_eq_of_le_normalizer
        refine (hZgJ'.trans hJ'C).trans
          ((Subgroup.centralizer_le hZleJ).trans (Subgroup.centralizer_le_normalizer _))
      apply hZJ
      have hZJ'' : Z ≤ J.map (MulAut.conj g).toMonoidHom := hZg ▸ hZgJ'
      exact hZJ''.trans hJ'C
    refine ⟨fun n hn g => ?_⟩
    rw [← hconj g]
    exact ⟨n, hn, rfl⟩
  refine h.concl_of_le ?_
  have hX : normalClosure (Z : Set G) ≤ J := Subgroup.normalClosure_le_normal hZleJ
  rw [← hrank]
  exact CFSG.SectionRank.pRank_mono h.prime.one_lt (hX.trans hJXY)

end Hyp

end CFSG.LocalAnalysis.UniquenessCase.UCK.N588A
